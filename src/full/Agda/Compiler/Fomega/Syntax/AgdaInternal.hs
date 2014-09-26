{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}  -- ghc >= 7.0

#if __GLASGOW_HASKELL__ >= 709
{-# LANGUAGE InstanceSigs          #-} -- too new, ghc >= 7.6
#endif

-- | Use 'Agda.Syntax.Internal' as representation of Fomega types.

module Agda.Compiler.Fomega.Syntax.AgdaInternal where

import Agda.Syntax.Common
-- import Agda.Syntax.Internal (Term(..))
import Agda.Syntax.Internal hiding (Type)
import qualified Agda.Syntax.Internal as I

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Compiler.Fomega.Syntax
import qualified Agda.Compiler.Fomega.Syntax as F

import Agda.Utils.Functor
import Agda.Utils.Maybe

#include "../../../undefined.h"
import Agda.Utils.Impossible

-- * Implementation of kinds.

type Kind     = I.Term
type KindView = KindView' Kind

-- | Kinds represented by terms of Agda's internal language of values,
--   using weak head evaluation on the type checking monad @TCM@.
instance KindRep TCM Kind where

#if __GLASGOW_HASKELL__ >= 709
  kindView :: Kind -> TCM KindView
#endif
  kindView t = do
    t <- reduce t
    case ignoreSharing t of
      -- KArrow is represented by I.Pi
      I.Pi dom b   -> return $ KArrow (unEl $ unDom dom) (unEl $ absBody b)
      -- KTerm is represented by I.Level (slight abuse)
      I.Level{}    -> return $ KTerm
      -- KType is represented by sort Set
      I.Sort{}     -> return $ KType
      -- The rest of Agda syntax is not used to represent kinds:
      I.Var{}      -> __IMPOSSIBLE__
      I.Def{}      -> __IMPOSSIBLE__
      I.Con{}      -> __IMPOSSIBLE__
      I.Lam{}      -> __IMPOSSIBLE__
      I.ExtLam{}   -> __IMPOSSIBLE__
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

instance TypeRep TCM Type where

  type KindRep_ Type = Kind


#if __GLASGOW_HASKELL__ >= 709
  -- typeView :: Type -> TCM TypeView
  typeView :: Type -> TCM (TypeView' (KindRep_ Type) Type)
#endif
  typeView t = do
    t <- reduce t
    case ignoreSharing t of
      -- Dependent function types are used to represent TForall,
      -- nondependent ones represent TArrow.
      I.Pi dom b   -> case b of
        Abs{}      -> return $ TForall (unEl $ unDom dom) (unEl <$> b)
        NoAbs _ b  -> return $ TArrow (unEl $ unDom dom) (unEl b)
      -- TLam is represented by Lam
      I.Lam _ t    -> return $ TLam t
      -- TVar is represented by Var, not using projection eliminations
      I.Var i es   -> return $ TVar (TyVar i) $ TyArgs $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- TCon is represented by Def, not using projection eliminations
      I.Def d es   -> return $ TCon d $ TyArgs $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      -- TErased is represented by Set
      I.Sort{}     -> return $ TErased
      -- TUnknown is represented as a string literate
      I.Lit{}      -> return $ TUnknown
      -- The rest of Agda syntax is not used:
      I.Con{}      -> __IMPOSSIBLE__
      I.ExtLam{}   -> __IMPOSSIBLE__
      I.Level{}    -> __IMPOSSIBLE__
      I.MetaV{}    -> __IMPOSSIBLE__
      I.DontCare{} -> __IMPOSSIBLE__
      I.Shared{}   -> __IMPOSSIBLE__

#if __GLASGOW_HASKELL__ >= 709
  tVar :: TVar -> TyArgs -> Type
#endif
  tVar i ts = I.Var (theTyVar i) $ map (Apply . defaultArg) $ theTyArgs ts

  tCon q ts = I.Def q $ map (Apply . defaultArg) $ theTyArgs ts
  tArrow t t' = I.Pi (defaultDom $ El Inf t) (NoAbs "_" $ El Inf t')
  tForall k t = I.Pi (defaultDom $ El Inf k) (El Inf <$> t)

#if __GLASGOW_HASKELL__ >= 709
  tLam :: I.Abs Type -> Type
#endif
  tLam t = I.Lam defaultArgInfo t

#if __GLASGOW_HASKELL__ >= 709
  tErased :: Type
#endif
  tErased = I.Sort $ mkType 0


-- -- * Expressions

-- type Expr = Term
-- type ExprView = ExprView' Expr
-- type Args = Args' Expr

-- instance ExprRep TCM Expr where

--   var i args = Var i $ map (Apply args

-- -}
