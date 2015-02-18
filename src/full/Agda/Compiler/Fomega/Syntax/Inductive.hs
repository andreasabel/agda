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

import Agda.Compiler.Fomega.Syntax
  ( KindRep(..), TypeRep(..), ExprRep(..)
  , TyVar(..), Var(..)
  , ArgInfo(..), Arg(..), Args'(..), TyArgs'(..), Elim(..), Elims'(..)
  )
import qualified Agda.Compiler.Fomega.Syntax as F

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
  = TVar {-# UNPACK #-} !TyVar TyArgs
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

type TyArgs = TyArgs' Type

-- | System F expressions.
data Expr
  = FVar {-# UNPACK #-} !Var Elims
    -- ^ Variables @x es@.
  | FLam ArgInfo (I.Abs Expr)
    -- ^ Term abstraction @λx.e@ or type abstraction @ΛX.e@.
  | FLit Literal
    -- ^ Constant numbers, strings, chars etc.
  | FDef QName Elims
    -- ^ Defined function @f es@.
  | FCon I.ConHead Args
    -- ^ Data constructor @c es@.
  | FCoerce Expr
    -- ^ Type cast (used for expressions that are well-typed in Agda,
    --   but ill-typed in Fω).

-- | List of arguments.
type Args = Args' Expr

-- | List of eliminations.
type Elims = Elims' (Arg Expr)

-- * Instantiating the abstract interface for kinds.

type KindView = F.KindView' Kind

instance KindRep Kind where
  kindView KType         = F.KType
  kindView KTerm         = F.KTerm
  kindView (KArrow k k') = F.KArrow k k'
  kType                  = KType
  kTerm                  = KTerm
  kArrow                 = KArrow


-- * Instantiating the abstract interface for types.

type TypeView = F.TypeView' Kind Type

instance TypeRep Kind Type where
  typeView t =
    case t of
      TVar x ts   -> F.TVar x ts
      TArrow t u  -> F.TArrow t u
      TForall k t -> F.TForall k t
      TCon d ts   -> F.TCon d ts
      TLam t      -> F.TLam t
      TUnknown    -> F.TUnknown
      TErased     -> F.TErased

  tVar x ts = TVar x ts
  tArrow    = TArrow
  tForall   = TForall
  tCon d ts = TCon d ts
  tLam      = TLam
  tUnknown  = TUnknown
  tErased   = TErased


-- * Instantiating the abstract interface for expressions.

type ExprView = F.ExprView' Expr

instance ExprRep Expr where
  exprView e =
    case e of
      FVar x es -> F.FVar x es -- (F.Elims $ map (F.Apply . unrepElim) es)
      FLam ai f -> F.FLam ai f
      FLit l    -> F.FLit l
      FDef d es -> F.FDef d es
      FCon c as -> F.FCon c as
      FCoerce e -> F.FCoerce e

  fVar      = FVar
  fLam      = FLam
  fLit      = FLit
  fDef      = FDef
  fCon      = FCon
  fCoerce   = FCoerce
