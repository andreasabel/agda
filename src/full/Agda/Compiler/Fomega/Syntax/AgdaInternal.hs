-- | Use 'Agda.Syntax.Internal' as representation of Fomega types.

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}  -- ghc >= 7.0

#if __GLASGOW_HASKELL__ >= 709
{-# LANGUAGE InstanceSigs          #-} -- too new, ghc >= 7.6
#endif

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
      I.Pi dom b   -> return $ KArrow (unEl $ unDom dom) (unEl $ absBody b)
      -- The following are not types:
      I.Lam{}      -> __IMPOSSIBLE__
      I.ExtLam{}   -> __IMPOSSIBLE__
      I.Lit{}      -> __IMPOSSIBLE__
      I.Con{}      -> __IMPOSSIBLE__
      I.Level{}    -> return $ KTerm
      -- The following is excluded by ignoreSharing.
      I.Shared{}   -> __IMPOSSIBLE__
      -- We cannot have an irrelevance marker in a type.
      I.DontCare{} -> __IMPOSSIBLE__
      -- We do not compile files with open metas.
      I.MetaV{}    -> __IMPOSSIBLE__
      -- Universes are collapsed into base kind *.
      I.Sort{}     -> return $ KType
      -- Neutral kinds are interpreted as base kind *.
      I.Var{}      -> return $ KType
      I.Def{}      -> return $ KType

#if __GLASGOW_HASKELL__ >= 709
  kType :: Kind
#endif
  kType     = Sort $ mkType 0
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
      I.Pi dom b   -> case b of
        NoAbs _ b  -> return $ TArrow (unEl $ unDom dom) (unEl b)
        Abs{}      -> return $ TForall (unEl $ unDom dom) (unEl <$> b)
      I.Lam _ t    -> return $ TLam t
      -- The following are not types:
      I.ExtLam{}   -> __IMPOSSIBLE__
      I.Lit{}      -> __IMPOSSIBLE__
      I.Con{}      -> __IMPOSSIBLE__
      I.Level{}    -> __IMPOSSIBLE__
      -- The following is excluded by ignoreSharing.
      I.Shared{}   -> __IMPOSSIBLE__
      -- We cannot have an irrelevance marker in a type.
      I.DontCare{} -> __IMPOSSIBLE__
      -- We do not compile files with open metas.
      I.MetaV{}    -> __IMPOSSIBLE__
      -- Universes are collapsed into base kind *.
      I.Sort{}     -> return $ TErased
      I.Var i es   -> return $ TVar i $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      I.Def d es   -> return $ TCon d $ map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

#if __GLASGOW_HASKELL__ >= 709
  tVar :: TVar -> TyArgs -> Type
#endif
  tVar i ts = I.Var i $ map (Apply . defaultArg) ts

  tCon q ts = I.Def q $ map (Apply . defaultArg) ts
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
