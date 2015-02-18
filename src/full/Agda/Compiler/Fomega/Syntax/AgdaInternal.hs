{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}  -- ghc >= 7.0

#if __GLASGOW_HASKELL__ >= 709
{-# LANGUAGE InstanceSigs          #-} -- too new, ghc >= 7.6
#endif

-- | Use 'Agda.Syntax.Internal' as representation of Fomega types.

module Agda.Compiler.Fomega.Syntax.AgdaInternal where

import Agda.Syntax.Common hiding (Arg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Literal
-- import Agda.Syntax.Internal (Term(..))
import Agda.Syntax.Internal hiding (Type, Var, Arg, ArgInfo)
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Compiler.Fomega.Syntax
import qualified Agda.Compiler.Fomega.Syntax as F

import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Null

#include "undefined.h"
import Agda.Utils.Impossible

-- * Implementation of kinds.

type Kind     = I.Term
type KindView = KindView' Kind

-- | Kinds represented by terms of Agda's internal language of values,
--   using weak head evaluation on the type checking monad @TCM@.
instance KindRep Kind where

#if __GLASGOW_HASKELL__ >= 709
  kindView :: Kind -> KindView
#endif
  kindView t =
    case ignoreSharing t of
      -- KArrow is represented by I.Pi
      I.Pi dom b   -> KArrow (unEl $ unDom dom) (unEl $ absBody b)
      -- KTerm is represented by I.Level (slight abuse)
      I.Level{}    -> KTerm
      -- KType is represented by sort Set
      I.Sort{}     -> KType
      -- The rest of Agda syntax is not used to represent kinds:
      I.Var{}      -> __IMPOSSIBLE__
      I.Def{}      -> __IMPOSSIBLE__
      I.Con{}      -> __IMPOSSIBLE__
      I.Lam{}      -> __IMPOSSIBLE__
      I.Lit{}      -> __IMPOSSIBLE__
      I.MetaV{}    -> __IMPOSSIBLE__
      I.DontCare{} -> __IMPOSSIBLE__
      I.Shared{}   -> __IMPOSSIBLE__

#if __GLASGOW_HASKELL__ >= 709
  kType :: Kind
#endif
  kType = Sort $ mkType 0
  -- Note: we do not care about the sort here.

  -- | We abuse Level to represent KTerm.
  kTerm = Level $ Max []

#if __GLASGOW_HASKELL__ >= 709
  kArrow :: Kind -> Kind -> Kind
#endif
  kArrow k k' = Pi (defaultDom $ El Inf k) (NoAbs "_" $ El Inf k')


-- * Implementation of types.

type Type     = I.Term
type TyArgs   = TyArgs' Type
type TypeView = TypeView' Kind Type

instance TypeRep Kind Type where

#if __GLASGOW_HASKELL__ >= 709
  -- typeView :: Type -> TCM TypeView
  typeView :: Type -> (TypeView' (KindRep_ Type) Type)
#endif
  typeView t =
    case ignoreSharing t of
      -- Dependent function types are used to represent TForall,
      -- nondependent ones represent TArrow.
      I.Pi dom b   -> case b of
        Abs{}      -> TForall (unEl $ unDom dom) (unEl <$> b)
        NoAbs _ b  -> TArrow (unEl $ unDom dom) (unEl b)
      -- TLam is represented by Lam
      I.Lam _ t    -> TLam t
      -- TVar is represented by Var, not using projection eliminations
      I.Var i es   -> TVar (TyVar i) $ TyArgs
                      $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- TCon is represented by Def, not using projection eliminations
      I.Def d es   -> TCon d $ TyArgs
                      $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- TErased is represented by Set
      I.Sort{}     -> TErased
      -- TUnknown is represented as a string literate
      I.Lit{}      -> TUnknown
      -- The rest of Agda syntax is not used:
      I.Con{}      -> __IMPOSSIBLE__
      I.Level{}    -> __IMPOSSIBLE__
      I.MetaV{}    -> __IMPOSSIBLE__
      I.DontCare{} -> __IMPOSSIBLE__
      I.Shared{}   -> __IMPOSSIBLE__

#if __GLASGOW_HASKELL__ >= 709
  tVar :: TVar -> TyArgs -> Type
#endif
  tVar    i ts = I.Var (theTyVar i) $ map (I.Apply . defaultArg) $ theTyArgs ts
  tCon    q ts = I.Def q $ map (I.Apply . defaultArg) $ theTyArgs ts
  tArrow  t t' = I.Pi (defaultDom $ El Inf t) (NoAbs "_" $ El Inf t')
  tForall k t  = I.Pi (defaultDom $ El Inf k) (El Inf <$> t)

#if __GLASGOW_HASKELL__ >= 709
  tLam :: I.Abs Type -> Type
#endif
  tLam t = I.Lam defaultArgInfo t

#if __GLASGOW_HASKELL__ >= 709
  tErased :: Type
#endif
  tErased  = I.Sort $ mkType 0
  tUnknown = I.Lit  $ LitString empty "NotFomegaType"


-- -- * Expressions

type Expr = Term
type ExprView = ExprView' Expr
type Args = Args' Expr

-- TypeArg is represented as Irrelevant
-- TermArg as Relevant

repArgInfo :: ArgInfo -> I.ArgInfo
repArgInfo TermArg = defaultArgInfo
repArgInfo TypeArg = setRelevance Irrelevant defaultArgInfo

unrepArgInfo :: I.ArgInfo -> ArgInfo
unrepArgInfo ai = if getRelevance ai == Irrelevant then TypeArg else TermArg

repArg :: Arg a -> I.Arg a
repArg (Arg ai v) = Common.Arg (repArgInfo ai) v

unrepElim :: I.Elim' a -> Arg a
unrepElim Proj{}      = __IMPOSSIBLE__
unrepElim (I.Apply a) = unrepArg a

unrepArg :: I.Arg a -> Arg a
unrepArg (Common.Arg ai v) = Arg (unrepArgInfo ai) v where

instance ExprRep Expr where
  -- Representation of Fomega expressions in Agda terms
  fVar (Var i) (Args vs) = I.Var i $ map (Apply . repArg) vs
  fLam ai b              = I.Lam (repArgInfo ai) b
  fLit l                 = I.Lit l
  fDef f (Args vs)       = I.Def f $ map (Apply . repArg) vs
  fCon c (Args vs)       = I.Con c $ map repArg vs
  fCoerce v              = I.Level $ I.Max [I.Plus 0 $ UnreducedLevel v]

  exprView v =
    case ignoreSharing v of
      I.Var i es -> FVar (Var i) $ Args $ map unrepElim es
      I.Lam ai b -> FLam (unrepArgInfo ai) b
      I.Lit l    -> FLit l
      I.Def f es -> FDef f $ Args $ map unrepElim es
      I.Con c vs -> FCon c $ Args $ map unrepArg vs
      I.Level (I.Max [I.Plus 0 (I.UnreducedLevel v)]) -> FCoerce v
      _          -> __IMPOSSIBLE__

