{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | Compile Agda to System Fω with data types and constructor.
--
--   Abstract interfaces to the syntax of System Fω in terms of
--   views and construction functions.

module Agda.Compiler.Fomega.Syntax where

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

-- * Kinds

-- | System F omega kinds.
--   Proper kinds are of the form @κ₁ → ... → κₗ → ⋆@
--   where the @κᵢ@ can be arbitrary kinds (including @KTerm@).
data KindView' a
  = KType
    -- ^ Kind of types ⋆.
  | KTerm
    -- ^ Kind of terms @()@.
    --   May only appear as @() → κ@ in proper kinds.
  | KArrow a a
    -- ^ Function kind (kind of type constructors) @κ → κ'@.

class Monad m => KindRep m a where
  kindView :: a -> m (KindView' a)
  -- ^ View @a@ as kind.
  kType    :: a
  -- ^ Construct the kind @*@ of types.
  kTerm    :: a
  -- ^ Construct the kind @()@ of terms.
  kArrow   :: a -> a -> a
  -- ^ Construct a function kind.

-- * Types

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

-- ** Class interface

-- | Interface to Fω types in β-normal form.
--   @a@ is a representation of Fomega types.

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

-- | System Fω expressions in β-normal form.
--   Note: 'Agda.Syntax.Internal' has already only β-normal forms.
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

-- ** Class interface

class Monad m => ExprRep m a where

  exprView :: a -> m (ExprView' a)
  -- ^ View @a@ as expression.

  fVar :: Var -> Args' a -> a
  -- ^ Construct a neutral expression.
  fLam :: ArgInfo -> I.Abs a -> a
  -- ^ Construct a lambda abstraction.
  fLit :: Literal -> a
  -- ^ Construct a literal expression.
  fDef :: QName -> Args' a -> a
  -- ^ Construct a definition application.
  fCon :: I.ConHead -> Args' a -> a
  -- ^ Construct a constructor application.
  fCoerce :: a -> a
  -- ^ Construct a coerced expression.
