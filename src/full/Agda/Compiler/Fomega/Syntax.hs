{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternGuards              #-}

-- | Compile Agda to System Fω with data types and constructor.
--
--   Abstract interfaces to the syntax of System Fω in terms of
--   views and construction functions.

module Agda.Compiler.Fomega.Syntax where

import Data.Monoid
import Data.Foldable    (Foldable)
import Data.Traversable (Traversable)

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
  ( defaultArgInfo
  , Relevance(..), LensRelevance(..)
  )
import qualified Agda.Syntax.Common as Common
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

import Agda.Utils.Null
import Agda.Utils.Singleton

#include "undefined.h"
import Agda.Utils.Impossible

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

class KindRep a where
  kindView :: a -> KindView' a
  -- ^ View @a@ as kind.
  kType    :: a
  -- ^ Construct the kind @*@ of types.
  kTerm    :: a
  -- ^ Construct the kind @()@ of terms.
  kArrow   :: a -> a -> a
  -- ^ Construct a function kind.

newtype WrapKind a = WrapKind { wrappedKind :: a }
  deriving (Eq, Ord, Show)

-- * Types

-- ** Standard view

-- | System F omega types and type constructors.
data TypeView' k a
  = TVar {-# UNPACK #-} !TyVar (TyArgs' a)
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

-- | Type variables are represented by de Bruijn indices.
newtype TyVar = TyVar { theTyVar :: Int }
  deriving (Eq, Ord, Show, Num)

newtype TyArgs' a = TyArgs { theTyArgs :: [a] }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Null, Singleton a, Monoid)

-- ** Class interface

-- | Interface to Fω types in β-normal form.
--   @a@ is a representation of Fomega types.

class TypeRep k a | a -> k where
  typeView :: a -> TypeView' k a
  -- ^ View @a@ as a type.
  tVar :: TyVar -> TyArgs' a -> a
  -- ^ Construct a neutral application.
  tArrow :: a -> a -> a
  -- ^ Construct a function type.
  tForall :: k -> I.Abs a -> a
  -- ^ Construct a polymorphic type.
  tCon :: QName -> TyArgs' a -> a
  -- ^ Construct a type constructor application.
  tLam :: I.Abs a -> a
  -- ^ Construct a type-level lambda.
  tUnknown :: a
  -- ^ Construct an unknown type.
  tErased  :: a
  -- ^ Construct an erasure marker.

  -- | View @a@ as a function type.
  funTypeView :: a -> FunTypeView' k a
  funTypeView t =
    let v = typeView t
    in case v of
      TArrow a b
        | TErased <- typeView a -> FTEraseArg b
        | otherwise             -> FTArrow a b
      TForall k f -> FTForall k f
      _           -> FTNo

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

newtype WrapType a = WrapType { wrappedType :: a }
  deriving (Eq, Ord, Show)

-- * Expressions

-- | System Fω expressions in β-normal form.
--   Note: 'Agda.Syntax.Internal' has already only β-normal forms.
data ExprView' a
  = FVar {-# UNPACK #-} !Var (Elims' (Arg a))
    -- ^ Variables @x es@.
  | FLam ArgInfo (I.Abs a)
    -- ^ Term abstraction @λx.e@ or type abstraction @ΛX.e@.
  | FLit Literal
    -- ^ Constant numbers, strings, chars etc.
  | FDef QName (Elims' (Arg a))
    -- ^ Defined function @f es@.
  | FCon I.ConHead (Args' a)
    -- ^ Data constructor @c es@.
  | FCoerce a
    -- ^ Type cast (used for expressions that are well-typed in Agda,
    --   but ill-typed in Fω).
  | FDummy
    -- ^ Dummy expression.

-- | Term variables are de Bruijn indices.
newtype Var = Var { theVar :: Int }
  deriving (Eq, Ord, Show, Num)

-- | Classification of arguments in expression application.
data ArgInfo
  = TypeArg
    -- ^ Type argument.
  | TermArg
    -- ^ Term argument.
  deriving (Eq, Ord, Show)

-- | Decorated arguments.
data Arg a = Arg
  { argInfo :: ArgInfo
    -- ^ Argument decoration.
  , arg     :: a
    -- ^ The argument.
  } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | List of arguments.
newtype Args' a = Args { theArgs :: [Arg a] }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Null)

-- | Eliminations are either arguments or coercions.
data Elim a
  = Coerce   -- ^ We need to coerce before we can apply to the next argument.
  | Apply a  -- ^ The next argument.
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | List of eliminations.
newtype Elims' a = Elims { theElims :: [Elim a] }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Null)

-- ** Class interface

class ExprRep a where
  exprView :: a -> ExprView' a
  -- ^ View @a@ as expression.
  fVar :: Var -> Elims' (Arg a) -> a
  -- ^ Construct a neutral expression.
  fLam :: ArgInfo -> I.Abs a -> a
  -- ^ Construct a lambda abstraction.
  fLit :: Literal -> a
  -- ^ Construct a literal expression.
  fDef :: QName -> Elims' (Arg a) -> a
  -- ^ Construct a definition application.
  fCon :: I.ConHead -> Args' a -> a
  -- ^ Construct a constructor application.
  fCoerce :: a -> a
  -- ^ Construct a coerced expression.
  fDummy :: a
  -- ^ Construct a dummy expression
  -- (e.g., when extracting something that is not a Fomega expression).


------------------------------------------------------------------------
-- Show Instances
------------------------------------------------------------------------

-- TODO: nicer Show for newtypes
-- instance Show a => Show (WrapKind a) where
--   show (WrapKind a) = "WrapKind " ++ show a  -- precedence?
