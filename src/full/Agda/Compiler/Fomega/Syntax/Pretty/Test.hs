{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Agda.Compiler.Fomega.Syntax.Pretty.Test where

import Control.Monad.Identity

import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Abstract.Name (qualify_, QName(..), MkName(..))
import qualified Agda.Syntax.Internal as I

import Agda.Compiler.Fomega.Syntax
  ( WrapKind(..), WrapType(..)
  , TyVar(..), Var(..)
  , TyArgs'(..)
  )
import Agda.Compiler.Fomega.Syntax.Inductive
import Agda.Compiler.Fomega.Syntax.Inductive.Pretty
import Agda.Compiler.Fomega.Syntax.Pretty

import Agda.Utils.NameContext
import Agda.Utils.Null
import Agda.Utils.Pretty

k0 = KType `KArrow` KType
k1 = k0 `KArrow` k0

type Cxt = SizedIntNameMap Name ()

type PrintM a = NameT Cxt UsedNameSet (PrecT FPrec Identity) a

runPrinter :: PrintM a -> a
runPrinter = runIdentity . runPrecT . evalNameT_

printKind :: Kind -> Doc
printKind = runPrinter . prettyPrecM

k0' = printKind k0
k1' = printKind k1

-- doPrint ::
-- doPrint a = evalNameT (prettyPrecM a) (empty :: )

printType :: Type -> Doc
printType = runPrinter . prettyPrecM

tyVar x = TVar (TyVar x) empty
tyCon x ts = TCon x (TyArgs ts)

t0 = TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyVar 0
t0' = printType t0

t1 = TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` t0
t1' = printType t1

t2 = TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` (TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyVar 1)
t2' = printType t2

qname :: String -> QName
qname = qualify_ . mkName_ (Common.NameId 0 0)

t3 = TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyCon (qname "A") [(TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyVar 1)]
t3' = printType t3

t4 = TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyCon (qname "List") [(TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyVar 1)]
t4' = printType t4

t5 = TForall KType $ I.Abs "A" $ tyCon (qname "List") [(TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyVar 1)] `TArrow`  tyVar 0 `TArrow` tyCon (qname "A") []
t5' = printType t5

t6 = TForall KType $ I.Abs "A" $ tyCon (qname "List") [(TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` tyCon (qname "A") [])] `TArrow`  tyVar 0 `TArrow` tyCon (qname "A") []
t6' = printType t6


t7 = TForall KType $ I.Abs "A" $ tyCon (qname "List") [(TForall KType $ I.Abs "A" $ tyVar 0 `TArrow` (tyVar 1 `TArrow` tyCon (qname "A") []))] `TArrow`  tyVar 0 `TArrow` tyCon (qname "A") []
t7' = printType t7
