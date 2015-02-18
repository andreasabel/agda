{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}  -- ghc >= 7.0

-- | Extracting Agda terms to Fomega kinds, types, and expressions.
--
-- Example:
-- @
--   data Vec (a : Level) (A : Set a) : ℕ → Set a where
--     nil  : Vec a A zero
--     cons : (n : ℕ) → A → Vec a A n → Vec a A (suc n)
--
--   data Fin : ℕ → Set where
--     zero : (n : ℕ) → Fin (suc n)
--     suc  : (n : ℕ) → Fin n → Fin (suc n)
--
--   lookup : (a : Level) (A : Set a) (n : ℕ) (i : Fin n) (v : Vec A n) → A
--   lookup a A .(suc m) (zero m) (cons .m x xs) = x
--   lookup a A .(suc m) (suc m i) (cons .m x xs) = lookup a A m i xs
--
-- @
-- represented as
-- @
--   data Vec  : (a : Level) → Set a → ℕ → Set a
--   con  nil  : (a : Level) (A : Set a) → Vec a A zero
--   con  cons : (a : Level) (A : Set a) →
--               (n : ℕ) → A → Vec a A n → Vec a A (suc n)
--
--   data Fin  : ℕ → Set
--   con  zero : (n : ℕ) → Fin (suc n)
--   con  suc  : (n : ℕ) → Fin n → Fin (suc n)
--
--   lookup : (a : Level) (A : Set a) (n : ℕ) (i : Fin n) (v : Vec A n) → A
--   lookup a A n i v =
--     case i of
--       zero m  ->
--         case v of
--           cons _ x xs -> x
--       suc m i ->
--         case v of
--           cons _ x xs -> lookup a A m i xs
-- @
-- is extracted to
-- @
--   data Vec  : () → * → () → *
--   con  nil  : () → ∀ A:*. Vec () A ()
--   con  cons : () → ∀ A:*. ℕ → A → Vec () A () → Vec () A ()
--
--   data Fin  : () → *
--   con  zero : ℕ → Fin ()
--   con  suc  : ℕ → Fin () → Fin ()
--
--   lookup : () → ∀ A : *.  ℕ → Fin () → Vec A () → A
--   lookup a A n i v =
--     case i of
--       zero m  ->
--         case v of
--           cons _ _ _ x xs -> x
--       suc m i ->
--         case v of
--           cons _ _ _ x xs -> lookup a A m i xs
-- @
-- Uninteresting arguments are discarded:
-- @
--   data Vec  : * → *
--   con  nil  : ∀ A:*. Vec A
--   con  cons : ∀ A:*. ℕ → A → Vec A → Vec A
--
--   data Fin  : *
--   con  zero : ℕ → Fin
--   con  suc  : ℕ → Fin → Fin
--
--   lookup : ∀ A : *.  ℕ → Fin → Vec A → A
--   lookup A n i v =
--     case i of
--       zero m  ->
--         case v of
--           cons _ _ x xs -> x
--       suc m i ->
--         case v of
--           cons _ _ x xs -> lookup A m i xs
-- @
-- which should be translated to Haskell as
-- @
--   data Vec a
--     = Nil
--     | Cons ℕ a (Vec a)
--
--   data Fin
--     = Zero ℕ
--     | Suc ℕ Fin
--
--  lookup : forall a. ℕ → Fin → Vec a → a
--  lookup n i v =
--    case i of
--      Zero m ->
--        case v of
--          Cons _ x xs -> x
--      Suc m i ->
--        case v of
--          Cons _ x xs -> lookup m i v
-- @

module Agda.Compiler.Fomega.Extract where

import Control.Applicative hiding (empty)

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

import Agda.Syntax.Common hiding (Dom, Arg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Literal
-- import Agda.Syntax.Internal (Term(..))
import Agda.Syntax.Internal hiding (Type, Arg, ArgInfo, Var)
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Compiler.Fomega.Syntax as F
import Agda.Compiler.Fomega.Syntax.AgdaInternal (Kind, Type, Expr)
-- import Agda.Compiler.Fomega.Syntax.Inductive (Expr)

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

-- | Extraction monad.
type Extract = TCM

-- * Kinds.

-- | Interpret an Agda type as Fomega kind.
--
--   Sorts @Set l@ are interpreted as base kind @*@.
--
--   (Dependent) function types @(x : T) → T' x@ are interpreted as
--   (non-dependent) function kinds @κ → κ'@.
--
--   Examples:
--
--     @Set -> Set1@ is extracted as @* -> *@.
--
--     @(A : Set) -> A@ does not correspond to a kind.
--
--     @T b@ does not correspond to a kind, where
--
--     @
--     T : Bool -> Set1
--     T true  = Set0 -> Set0
--     T false = Set0
--     @
--
--     @Set → ℕ → Set@ is extracted as @⋆ → () → ⋆@
--
class ExtractKind a where

  -- | Extract a kind from something.
  --   Can fail if that something does not correspond to an Fomega kind.
  extractKind  :: a -> Extract (Maybe Kind)
  extractKind a = runMaybeT $ extractKind' a

  extractKind' :: a -> MaybeT Extract Kind
  extractKind' a = MaybeT $ extractKind a

  -- | Extract an extended kind.
  --   Returns @kTerm@ if extracted kind is not proper.
  extractKindDom :: a -> Extract Kind
  extractKindDom a = fromMaybe kTerm <$> extractKind a

instance ExtractKind I.Term where
  extractKind' v = do
    v <- liftTCM $ reduce v
    case ignoreSharing v of
      I.Sort{}   -> pure $ kType
      I.Pi dom b -> kArrow <$> lift (extractKindDom dom)
                           <*> extractKind' (absApp b dummy)
      _        -> mzero
    where
      dummy = I.Lit $ LitString empty $
        "VariableSubstitutedDuringKindExtraction"

instance ExtractKind I.Type where
  extractKind' = extractKind' . unEl

instance ExtractKind a => ExtractKind (Dom a) where
  extractKind' = extractKind' . unDom

-- * Types.

-- | Extract a Fomega type from an Agda expression.
--
--   Examples:
--
--   @(X : Set) -> X@ is extracted to @∀ X:⋆. X@.
--   @(n : ℕ) → Vec X n@ is extracted to @ℕ → Vec X ()@.
class ExtractType a where
  extractType      :: a -> Extract Type
  extractTypeAt    :: Kind -> a -> Extract Type

instance ExtractType Term where
  extractType v = do
    v <- reduce v
    case ignoreSharing v of
      -- The following are not types:
      I.Lam{}    -> __IMPOSSIBLE__
      I.Lit{}    -> __IMPOSSIBLE__
      I.Con{}    -> __IMPOSSIBLE__
      -- Neutral types:
      I.Var i es    -> do
        caseMaybe (allApplyElims es) (return tUnknown) $ \ args -> do
        t <- typeOfBV i
        tVar (TyVar i) <$> extractTypeArgs t args
      -- Data types and stuck defined types:
      I.Def d es -> do
        caseMaybeM (isDataOrRecordType d) (return tUnknown) $ \ _ -> do
        -- @d@ is data or record constructor:
        t <- defType <$> getConstInfo d
        let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        tCon d <$> do extractTypeArgs t args
      -- Function types and polymorphic types
      I.Pi dom b -> do
        let x = absName b
        mk <- extractKind dom
        case mk of
          -- If @dom@ is a kind @κ@, we return a polymorphic type @∀X:κ.T@.
          Just k -> tForall k . mkAbs x <$> do
            addContext (x, dom) $  -- OR: (x, defaultDom mk) !?
              extractType (absBody b)
          -- Otherwise, a function type @U → T@.
          Nothing  -> tArrow <$> extractType dom
                             <*> extractType (absApp b dummy)
      -- Universes and Level carry no runtime content:
      I.Sort{}     -> return tErased
      I.Level{}    -> return tErased
      -- A meta variable can stand for anything.
      I.MetaV{}    -> return tUnknown
      I.DontCare v -> return tErased
      I.Shared{}   -> __IMPOSSIBLE__
    where
      dummy = I.Lit $ LitString empty "VariableSubstitutedDuringTypeExtraction"

  extractTypeAt k t =        -- similar to extractTermCheck
    case kindView k of
      KType         -> extractType t
      KTerm         -> tErased
      KArrow k1 k2  -> do

        case ignoreSharing t of

          Lam ai b -> tLam . Abs (absName b) <$>
            underAbs k1 b $ \ v -> extractTypeAt k2 v

          _ -> do
            let x = stringToArgName "X"
            tLam . Abs x <$>
              addContext (x, k1) $
                extractTypeAt k2 $ raise 1 t `apply` defaultArg (Var 0)

    where underAbs t = underAbstraction (defaultDom (El I.Inf t))



-- similar to extractArgs
extractTypeArgs = undefined

instance ExtractType I.Type where
  extractType = extractType . unEl

instance ExtractType a => ExtractType (Dom a) where
  extractType = extractType . unDom






-- * Terms

{-

Bidirectional extraction
========================

Types

  Base ::= D As         data type
         | ?            inexpressible type

  A,B ::= Base | A -> B | [x:K] -> B | [] -> B  with erasure markers
  A0, B0 ::= Base | A0 -> B0 | [x:K0] -> B0     without erasure markers

  |.| erase erasure markers

Inference mode:

  Term extraction:  Gamma |- t :> A  --> e    |Gamma| |- e : |A|
  Type extraction:  Gamma |- T :> K  --> A    |Gamma| |- A : |K|
  Kind extraction:  Gamma |- U :> [] --> K    |Gamma| |- K : []

Checking mode:

  Term extraction:  Gamma |- t <: A  --> e    |Gamma| |- e : |A|
  Type extraction:  Gamma |- T <: K  --> A    |Gamma| |- A : |K|
  Kind extraction:  Gamma |- U <: [] --> K    |Gamma| |- K : []

Type and kind extraction keep erasure markers!

Checking abstraction:

  Relevant abstraction:
  Gamma, x:A |- t <: B --> e
  --------------------------------
  Gamma |- \x.t <: A -> B --> \x.e

  Type abstraction:
  Gamma, x:K |- t <: B --> e : B0
  ----------------------------------------
  Gamma |- \[x].t <: [x:K] -> B --> \[x].e
      also \xt

  Irrelevant abstraction:
  Gamma |- t : B --> e
  -------------------------------
  Gamma |- \[x].t : [] -> B --> e
      also \xt

  Relevant abstraction at unknown type:
  Gamma, x:? |- t : ? --> e
  --------------------------
  Gamma |- \x.t : ? --> \x.e

  Irrelevant abstraction at unknown type:
  Gamma |- t : ? --> e
  -------------------------
  Gamma |- \[x].t : ? --> e

Checking by inference:

  Gamma |- t :> A --> e    e : |A| <: |B| --> e'
  ----------------------------------------------
  Gamma |- t <: B --> e' : B0

Casting:

  ------------------ A0 does not contain ?
  e : A0 <: A0 --> e

  ----------------------- A0 != B0 or one does contain ?
  e : A0 <: B0 --> cast e

Inferring variable:

  ----------------------------
  Gamma |- x :> Gamma(x) --> x

Inferring application:

  Relevant application:
  Gamma |- t :> A -> B --> f     Gamma |- u <: A --> e
  ----------------------------------------------------
  Gamma |- t u :> B --> f e

  Type application:
  Gamma |- t :> [x:K] -> B --> f   Gamma |- u <: K --> A
  ------------------------------------------------------
  Gamma |- t [u] :> : B[A/x] --> f [A]
      also  t u

  Irrelevant application:
  Gamma |- t :> [] -> B --> f
  ---------------------------
  Gamma |- t [u] :> B --> f
      also  t u

  Relevant application at unknown type:
  Gamma |- t :> ? --> f     Gamma |- u <: ? --> e
  -----------------------------------------------
  Gamma |- t u :> ? --> f e

  Irrelevant application at unknown type:
  Gamma |- t :> ? --> f
  -------------------------
  Gamma |- t [u] :> ? --> f



-}

class ExtractTerm a where
  extractTermCheck :: a -> Type -> Extract Expr
  extractTermInfer :: a -> Extract (Expr, Type)
  extractArg       :: Type -> I.Arg a
                   -> (Type -> [F.Elim (F.Arg Expr)] -> Extract a) -> Extract a
  extractArgs      :: Type -> [I.Arg a] -> Extract ([Arg Expr], Type)
  extractElims     :: Type -> [I.Elim' a] -> Extract ([F.Elim (F.Arg Expr)], Type)


instance ExtractTerm Term where
  extractTermCheck v a = do
    case ignoreSharing v of
      Lam ai b -> do
        let x = absName b
        case funTypeView a of
          FTArrow t u -> fLam TermArg . Abs x <$> do
            underAbs t b $ \ v -> do
              extractTermCheck v u
          FTForall k f -> fLam TypeArg . Abs x <$> do
            underAbs k b $ \ v -> do
              extractTermCheck v (absBody f)
          FTEraseArg u -> strengthen __IMPOSSIBLE__ <$> do
            underAbs tErased b $ \ v -> do
              extractTermCheck v u
          FTNo -> fCoerce <$> do
            if getRelevance ai `elem` [Irrelevant, UnusedArg, Forced]
             then strengthen __IMPOSSIBLE__ <$> do
                underAbs tErased b $ \ v -> do
                  extractTermCheck v tUnknown
             else fLam TermArg . Abs x <$> do
                underAbs tUnknown b $ \ v -> do
                  extractTermCheck v tUnknown
      _ -> do
        (e, t) <- extractTermInfer v
        ifM (tryConversion $ compareTerm CmpLeq topSort t a) (return e) $ {- else -}
          return $ fCoerce e

    where
      underAbs t = underAbstraction (defaultDom (El I.Inf t))

  extractTermInfer v = do
    case ignoreSharing v of
      I.Var i es -> do
        t <- typeOfBV i
        (es', t') <- extractElims (unEl t) es
        return (fVar (Var i) (Elims es'), t')
      I.Def f es -> do
        t <- typeOfConst f
        (es', t') <- extractElims (unEl t) es
        return (fDef f (Elims es'), t')
      I.Con c vs -> do
        let f = conName c
        t <- typeOfConst f
        (as, t') <- extractArgs (unEl t) vs
        return (fCon f (Argss as), t')
      _ -> __IMPOSSIBLE__


  extractArg canFTNo t (Common.Arg ai v) ret = do
    case funTypeView t of

      FTArrow a b -> do
        e <- extractTermCheck v a
        ret b [ F.Apply $ Arg TermArg e ]

      FTForall k f -> do
        g <- extractTypeAt v k
        ret (absApp f g) [ F.Apply $ Arg TypeArg g ]

      FTEraseArg a -> ret a []

      FTNo -> do
        (e, _t) <- extractTermInfer v
        ret tUnknown [Coerce, F.Apply (Arg TermArg e)]

  extractElims t es = do
    case es of
      []                 -> return ([], t)
      (I.Proj{}  : _)    -> __IMPOSSIBLE__
      (I.Apply arg : es) -> extractArg t arg $ \ t0 es0 -> do
         (es', t') <- extractElims t0 es
         return (es0 ++ es', t')

  extractArgs t args = do
    case args of
      []         -> return ([], t)
      (arg : as) -> extractArg t arg $ \ t0 es0 -> do
         -- Constructor types are always function types, so
         -- no coercions possible.
         let as0 = map elimToArg es0
         (as', t') <- extractArgs t0 as
         return (as0 ++ as', t')

elimToArg (F.Coerce{}) = __IMPOSSIBLE__
elimToArg (F.Apply a)  = a

{-
  extractElims t es = do
    case es of
      [] -> return ([], t)
      (I.Proj{}  : _) -> __IMPOSSIBLE__
      (I.Apply (Common.Arg ai v) : es) -> do
         case funTypeView t of
           FTArrow a b -> do
             e'        <- extractTermCheck v a
             (es', t') <- extractElims b es
             return (I.Apply (Arg TermArg e') : es', t')
           FTForall k f -> do
             g <- extractTypeAt v k
             (es', t') <- extractElims (absApp f g) es
             return (I.Apply (Arg TypeArg g : es'), t')
           FTEraseArg a -> extractElims a es
           FTNo -> do
             (e, t) <- extractTermInfer v
             (es, t') <- extractElims tUnknown es
             return ([Coerce, I.Apply (Arg TermArg e)] ++ es, t')
-}

-- -}
