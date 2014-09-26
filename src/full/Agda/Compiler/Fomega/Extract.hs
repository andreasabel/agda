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

import Control.Monad.Trans.Maybe

import Agda.Syntax.Common
-- import Agda.Syntax.Internal (Term(..))
import Agda.Syntax.Internal hiding (Type)
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Compiler.Fomega.Syntax
-- import qualified Agda.Compiler.Fomega.Syntax as F

import Agda.Utils.Functor
import Agda.Utils.Maybe

#include "../../undefined.h"
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

instance ExtractKind Term where
  extractKind' v = do
    v <- reduce v
    case ignoreSharing v of
      Sort{}   -> pure $ kType
      Pi dom b -> kArr <$> lift (extractKindDom dom)
                       <*> extractKind' (absApp b dummy)
      _        -> mzero
    where
      dummy = Literal $ LitString noRange $
        "VariableSubstitutedDuringKindExtraction"

instance ExtractKind Type where
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
  extractType :: a -> Extract Type

instance ExtractType Term where
  extractType v = do
    v <- reduce v
    case ignoreSharing v of
      -- The following are not types:
      Lam{}    -> __IMPOSSIBLE__
      ExtLam{} -> __IMPOSSIBLE__
      Lit{}    -> __IMPOSSIBLE__
      Con{}    -> __IMPOSSIBLE__
      -- Neutral types:
      Var i es    -> do
        t <- typeOfBV i
        tVar i <$> extractTypeElims t es
      -- Data types and stuck defined types:
      Def d es -> do
        caseMaybeM (isDataOrRecord d) (return tUnknown) $ \ _ -> do
        -- @d@ is data or record constructor:
        t <- defType <$> getConstInfo
        let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        tCon d <$> do extractTypeArgs t args
      -- Function types and polymorphic types
      Pi dom b -> do
        mk <- extractKind dom
        case mk of
          -- If @dom@ is a kind @κ@, we return a polymorphic type @∀X:κ.T@.
          Just k -> tForall k <$> do
            addContext dom $
              mkAbs (absName b) <$> extractType (absBody b)
          -- Otherwise, a function type @U → T@.
          Nothing -> tArrow <$> extractType dom
                            <*> extractType (absApp b dummy)
      -- Universes and Level carry no runtime content:
      Sort{}   -> tErased
      Level{}  -> tErased
      -- A meta variable can stand for anything.
      MetaV{}  -> tUnknown
      Shared{} -> __IMPOSSIBLE__
    where
      dummy = Literal $ LitString noRange $
        "VariableSubstitutedDuringTypeExtraction"

instance ExtractType I.Type where
  extractType = extractType . unEl

instance ExtractType a => ExtractType (Dom a) where
  extractType = extractType . unDom
