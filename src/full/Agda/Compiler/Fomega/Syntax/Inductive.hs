{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | Compile Agda to System Fω with data types and constructor.
--
--   Canonical (least) instance of System Fω syntax.

module Agda.Compiler.Fomega.Syntax.Inductive where

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

import Agda.Compiler.Fomega.Syntax (KindRep(..), TypeRep(..), ExprRep(..), ArgInfo(..), Arg(..))
import qualified Agda.Compiler.Fomega.Syntax as F

-- | System F omega kinds.
data Kind
  = KType
    -- ^ Kind of types ⋆.
  | KTerm
    -- ^ Kind of terms @()@.
  | KArrow Kind Kind
    -- ^ Function kind (kind of type constructors) @κ → κ'@.

-- | System F omega types and type constructors.
data Type
  = TVar {-# UNPACK #-} !TVar TyArgs
    -- ^ Type (constructor) variables (applied to types).
  | TArrow Type Type
    -- ^ Function type.
  | TForall Kind (I.Abs Type)
    -- ^ Polymorphic type.
  | TCon QName TyArgs
    -- ^ Data or record type constructor application.
  | TLam (I.Abs Type)
    -- ^ Type abstraction @λX.T@.
  | TUnknown
    -- ^ A type coming from Agda that is not representable in System Fω.
  | TErased
    -- ^ Type of erased things (proofs etc.)

type TyArgs = [Type]

-- | Type variables are represented by de Bruijn indices.
type TVar = Int

-- | System F expressions.
data Expr
  = FVar {-# UNPACK #-} !FVar Args
    -- ^ Variables @x es@.
  | FLam ArgInfo (I.Abs Expr)
    -- ^ Term abstraction @λx.e@ or type abstraction @ΛX.e@.
  | FLit Literal
    -- ^ Constant numbers, strings, chars etc.
  | FDef QName Args
    -- ^ Defined function @f es@.
  | FCon I.ConHead Args
    -- ^ Data constructor @c es@.
  | FCoerce Expr
    -- ^ Type cast (used for expressions that are well-typed in Agda,
    --   but ill-typed in Fω).

-- | Term variables are de Bruijn indices.
type FVar = Int

-- | List of arguments.
type Args = [Arg Expr]


-- * Instantiating the abstract interface for kinds.

type KindView = F.KindView' Kind

instance Monad m => KindRep m Kind where

  -- kindView :: Monad m => Kind -> m KindView
  kindView KType         = return $ F.KType
  kindView KTerm         = return $ F.KTerm
  kindView (KArrow k k') = return $ F.KArrow k k'

  kType  = KType
  kTerm  = KTerm
  kArrow = KArrow


-- * Instantiating the abstract interface for types.

type TypeView = F.TypeView' Kind Type

instance Monad m => TypeRep m Type where

  type KindRep_ Type = Kind

  -- typeView :: Monad m => Type -> m TypeView
  typeView t =
    case t of
      TVar i ts   -> return $ F.TVar i ts
      TArrow t u  -> return $ F.TArrow t u
      TForall k t -> return $ F.TForall k t
      TCon d ts   -> return $ F.TCon d ts
      TLam t      -> return $ F.TLam t
      TUnknown    -> return $ F.TUnknown
      TErased     -> return $ F.TErased

  tVar    = TVar
  tArrow  = TArrow
  tForall = TForall
  tCon    = TCon
  tLam    = TLam
  tErased = TErased


-- * Instantiating the abstract interface for expressions.

type ExprView = F.ExprView' Expr

instance Monad m => ExprRep m Expr where

  -- exprView :: Expr -> m ExprView
  exprView e =
    case e of
      FVar i es -> return $ F.FVar i es
      FLam ai f -> return $ F.FLam ai f
      FLit l    -> return $ F.FLit l
      FDef d es -> return $ F.FDef d es
      FCon c es -> return $ F.FCon c es
      FCoerce e -> return $ F.FCoerce e

  fVar    = FVar
  fLam    = FLam
  fLit    = FLit
  fDef    = FDef
  fCon    = FCon
  fCoerce = FCoerce
