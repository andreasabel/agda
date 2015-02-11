{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | Compile Agda to System Fω with data types and constructor.
--
--   Canonical (least) instance of System Fω syntax.

module Agda.Compiler.Fomega.Syntax.Inductive where

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Literal

import Agda.Compiler.Fomega.Syntax (KindRep(..), TypeRep(..), ExprRep(..), ArgInfo(..), Arg(..))
import qualified Agda.Compiler.Fomega.Syntax as F

-- compilation error: Could not find module ‘Agda.Compiler.Fomega.Syntax’ ?

-- | System F omega kinds.
data Kind
  = KType
    -- ^ Kind of types ⋆.
  | KTerm
    -- ^ Kind of terms @()@.
  | KArrow Kind Kind
    -- ^ Function kind (kind of type constructors) @κ → κ'@.
  deriving (Show)

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
  deriving (Show)

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
  kindView KType         = F.KType
  kindView KTerm         = F.KTerm
  kindView (KArrow k k') = F.KArrow k k'

  kType  = KType
  kTerm  = KTerm
  kArrow = KArrow


-- * Instantiating the abstract interface for types.

type TypeView = F.TypeView' Kind Type

instance Monad m => TypeRep m Kind Type where

  -- typeView :: Monad m => Type -> m TypeView
  typeView t =
    case t of
      TVar i ts   -> F.TVar (F.TyVar i) (F.TyArgs ts)
      TArrow t u  -> F.TArrow t u
      TForall k t -> F.TForall k t
      TCon d ts   -> F.TCon d (F.TyArgs ts)
      TLam t      -> F.TLam t
      TUnknown    -> F.TUnknown
      TErased     -> F.TErased

  tVar x ts = TVar (F.theTyVar x) (F.theTyArgs ts)
  tArrow    = TArrow
  tForall   = TForall
  tCon d ts = TCon d (F.theTyArgs ts)
  tLam      = TLam
  tUnknown  = TUnknown
  tErased   = TErased


-- * Instantiating the abstract interface for expressions.

type ExprView = F.ExprView' Expr

instance Monad m => ExprRep m Expr where

  -- exprView :: Expr -> m ExprView
  exprView e =
    case e of
      FVar i es -> F.FVar (F.Var i) (F.Args es)
      FLam ai f -> F.FLam ai f
      FLit l    -> F.FLit l
      FDef d es -> F.FDef d (F.Args es)
      FCon c es -> F.FCon c (F.Args es)
      FCoerce e -> F.FCoerce e

  fVar x es = FVar (F.theVar x) (F.theArgs es)
  fLam      = FLam
  fLit      = FLit
  fDef d es = FDef d (F.theArgs es)
  fCon c es = FCon c (F.theArgs es)
  fCoerce   = FCoerce
