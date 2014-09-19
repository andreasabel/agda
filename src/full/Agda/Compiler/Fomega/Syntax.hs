-- | Compile Agda to System Fω with data types and constructor.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}


module Agda.Compiler.Fomega.Syntax where


{- extract to Fomega

Examples:
---------

MiniAgda

  data Vec (A : Set) : Nat -> Set
  { vnil  : Vec A zero
  ; vcons : [n : Nat] -> (head : A) -> (tail : Vec A n) -> Vec A (suc n)
  } fields head, tail

  fun length : [A : Set] -> [n : Nat] -> Vec A n -> <n : Nat>
  { length .A .zero    (vnil A)         = zero
  ; length .A .(suc n) (vcons A n a as) = suc (length A n as)
  }

Fomega

  data Vec (A : Set) : Set
  { vnil  : Vec A
  ; vcons : (head : A) -> (tail : Vec A) -> Vec A
  }

  fun head : [A : Set] -> Vec A -> A
  { head (vcons 'head 'tail) = 'head
  }

  fun tail : [A : Set] -> Vec A -> A
  { head (vcons 'head 'tail) = 'tail
  }

  fun length : [A : Set] -> Vec A -> Nat
  { length [A]  vnil             = zero
  ; length [A] (vcons [.A] a as) = suc (length [A] as)
  }


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

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

-- * Kinds

-- | System F omega kinds.
data KindView' a
  = KBase
    -- ^ Kind of types ⋆.
  | KArr a a
    -- ^ Function kind (kind of type constructors) @κ → κ'@.

class Monad m => KindRep m a where
  kindView :: a -> m (KindView' a)
  -- ^ View @a@ as kind.
  kBase :: a
  -- ^ Construct the base kind.
  kArr  :: a -> a -> a
  -- ^ Construct a function kind.

-- * Types

-- | @a@ is a representation of Fomega types.
class Monad m => TypeRep m a where
  type KindRep_ a :: *
  -- ^ The representation of kinds.
  typeView :: a -> m (TypeView' (KindRep_ a) a)
  -- ^ View @a@ as a type.
  tVar :: TVar -> TyArgs' a -> a
  -- ^ Construct a neutral application.
  tArrow :: a -> a -> a
  -- ^ Construct a function type.
  tForall :: KindRep_ a -> I.Abs a -> a
  -- ^ Construct a polymorphic type.
  tCon :: QName -> TyArgs' a -> a
  -- ^ Construct a type constructor application.
  tLam :: I.Abs a -> a
  -- ^ Construct a type-level lambda.
  -- tUnknown :: a -- NEEDED?
  tErased  :: a
  -- ^ Construct an erasure marker.

  -- | View @a@ as a function type.
  funTypeView :: a -> m (FunTypeView' (KindRep_ a) a)
  funTypeView t = do
    v <- typeView t
    case v of
      TArrow a b  -> return $ FTArrow a b
      TForall k f -> return $ FTForall k f
      _ -> return $ FTNo

-- ** Standard view

-- | System F omega types and type constructors.
data TypeView' k a
  = TVar {-# UNPACK #-} !TVar (TyArgs' a)
    -- ^ Type (constructor) variables (applied to types).
  | TArrow a a
    -- ^ Function type @T → U@.
  | TForall k (I.Abs a)
    -- ^ Polymorphic type @∀ X:κ. T@.
  | TCon QName (TyArgs' a)
    -- ^ User defined data/record type constructor.
  | TLam (I.Abs a)
    -- ^ Type abstraction @λX.T@.
  | TUnknown
    -- ^ A type coming from Agda that is not representable in System Fω.
  | TErased
    -- ^ Type of erased things (proofs etc.)

type TyArgs' a = [a]

-- | Type variables are represented by de Bruijn indices.
type TVar = Int

-- ** Function type view

data FunTypeView' k a
  = FTArrow a a
    -- ^ We are a function type @A -> B@.
  | FTForall k (I.Abs a)
    -- ^ We are a polymorphic type @∀X:κ.A@.
  | FTEraseArg a
    -- ^ We are an irrelevant function type @. -> B@,
    --   arguments to functions should be erased.
  | FTNo
    -- ^ We are not a function type of any sort.


-- * Expressions

-- | System F expressions.
data ExprView' a
  = FVar {-# UNPACK #-} !Var (Args' a)
    -- ^ Variables @x es@.
  | FLam ArgInfo (I.Abs a)
    -- ^ Term abstraction @λx.e@ or type abstraction @ΛX.e@.
  | FLit Literal
    -- ^ Constant numbers, strings, chars etc.
  | FDef QName (Args' a)
    -- ^ Defined function @f es@.
  | FCon I.ConHead (Args' a)
    -- ^ Data constructor @c es@.
  | FCoerce a
    -- ^ Type cast (used for expressions that are well-typed in Agda,
    --   but ill-typed in Fω).

-- | Term variables are de Bruijn indices.
type Var = Int

-- | Classification of arguments in expression application.
data ArgInfo
  = TypeArg
    -- ^ Type argument.
  | TermArg
    -- ^ Term argument.

-- | Decorated arguments.
data Arg a = Arg
  { argInfo :: ArgInfo
    -- ^ Argument decoration.
  , arg     :: a
    -- ^ The argument.
  }

-- | List of arguments.
type Args' a = [Arg a]

class Monad m => ExprRep m a where

  exprView :: a -> m (ExprView' a)
  -- ^ View @a@ as expression.

  var :: Var -> Args' a -> a
  -- ^ Construct a neutral expression.
  lam :: ArgInfo -> I.Abs a -> a
  -- ^ Construct a lambda abstraction.
  lit :: Literal -> a
  -- ^ Construct a literal expression.
  def :: QName -> Args' a -> a
  -- ^ Construct a definition application.
  con :: I.ConHead -> Args' a -> a
  -- ^ Construct a constructor application.
  coerce :: a -> a
  -- ^ Construct a coerced expression.
