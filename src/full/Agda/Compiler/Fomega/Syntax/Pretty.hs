-- {-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverlappingInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TupleSections             #-}

-- | Pretty printer for Fω syntax

module Agda.Compiler.Fomega.Syntax.Pretty where

import Control.Applicative

import Data.Maybe

import Agda.Compiler.Fomega.Syntax

import qualified Agda.Syntax.Internal as I

import Agda.Utils.NameContext
import Agda.Utils.Pretty
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- * Symbols

dType, dTerm, dArrow, dForall, dLambda, dUnknown, dErased :: Doc
dType    = text "*"
dTerm    = text "()"
dArrow   = text "→" -- "->"
dForall  = text "∀" -- "forall"
dLambda  = text "λ" -- "\\"
dUnknown = text "?"
dErased  = text "()"

-- * Precedences

-- | Abstract specification of precedences.

class TopPrecedence p => Precedence p where
  precFunction     :: p -> p
  precArgument     :: p -> p
  precLambdaBody   :: p -> p
  precArrowDomain  :: p -> p
  precArrowRange   :: p -> p
  precForallDomain :: p -> p
  precForallBody   :: p -> p

  appBrackets      :: p -> Bool
  lamBrackets      :: p -> Bool
  arrowBrackets    :: p -> Bool
  forallBrackets   :: p -> Bool

-- | Changing precedences in 'MonadPrec' sub computation.

goFunction     = localPrec precFunction
goArgument     = localPrec precArgument
goLambdaBody   = localPrec precLambdaBody
goArrowDomain  = localPrec precArrowDomain
goArrowRange   = localPrec precArrowRange
goForallDomain = localPrec precForallDomain
goForallBody   = localPrec precForallBody

-- | Precendences for printing System Fω syntax.
--
--   * We need to record whether we are the rightmost expression
--     in the syntax tree, for printing of binders λ and ∀.
--
--   * We need precendences for → and application.

data FPrec
  = TopPrec
  | ArrowDomainPrec
  | ArrowRangePrec Bool -- ^ @True@ means rightmost in expression.
  | FunctionPrec
  | ArgumentPrec Bool -- ^ @True@ means rightmost in expression.

-- | Are we in rightmost position in a top or bracketed context?

rightmost :: FPrec -> Bool
rightmost TopPrec            = True
rightmost ArrowDomainPrec    = False
rightmost (ArrowRangePrec b) = b
rightmost FunctionPrec       = False
rightmost (ArgumentPrec b)   = b

instance TopPrecedence FPrec where
  topPrecedence = TopPrec

instance Precedence FPrec where

  precFunction     _ = FunctionPrec
  precArgument     p = ArgumentPrec   $ rightmost p
  precLambdaBody   _ = TopPrec
  precArrowDomain  _ = ArrowDomainPrec
  precArrowRange   p = ArrowRangePrec $ rightmost p
  precForallDomain _ = TopPrec
  precForallBody   _ = TopPrec

  appBrackets (ArgumentPrec _) = True
  appBrackets _                = False

  lamBrackets    = not . rightmost
  forallBrackets = not . rightmost

  arrowBrackets TopPrec          = False
  arrowBrackets ArrowRangePrec{} = False
  arrowBrackets _                = True

-- * Kinds

-- | Note: function space in domain @(k1 -> k2) -> k3@
--   vs. function space in range @k1 -> k2 -> k3@.
instance (Functor m, Applicative m, Monad m, Precedence p, PrettyM p m (WrapKind a)) => PrettyM p m (KindView' a) where
  prettyPrecM k =
    case k of
      KType        -> pure $ dType
      KTerm        -> pure $ dTerm
      KArrow k1 k2 -> parensIf arrowBrackets $ do
        fsep <$> sequence
          [ goArrowDomain $ prettyPrecM $ WrapKind k1
          , pure $ dArrow
          , goArrowRange  $ prettyPrecM $ WrapKind k2
          ]

-- | Printer for kind representation.

-- Needs GHC languages extensions, because it is "always applicable"
-- (type variables instead of type constructors in goal).
-- {-# LANGUAGE OverlappingInstances      #-}
-- {-# LANGUAGE UndecidableInstances      #-}
--
-- Why does GHC-7.8.3 insist on an "Applicative m" constraint here?!
instance (Applicative m, Precedence p, MonadPrec p m, KindRep m a) => PrettyM p m (WrapKind a) where
  prettyPrecM (WrapKind a) = prettyPrecM =<< kindView a

-- * Types

instance (Functor m, Applicative m, Precedence p, PrettyM p m k, PrettyM p m a, MonadName () m) => PrettyM p m (TypeView' k a) where
  prettyPrecM t = do
    case t of
      TUnknown   -> return $ dUnknown
      TErased    -> return $ dErased
      TArrow a b -> parensIf arrowBrackets $ do
        fsep <$> sequence
          [ goArrowDomain $ prettyPrecM a
          , pure $ dArrow
          , goArrowRange  $ prettyPrecM b
          ]

      TCon c as  -> appParens $ fsep . (pretty c :) <$> do
        goArgument $ mapM prettyPrecM $ theTyArgs as
      TVar i as  -> appParens $ fsep <$> do
        x <- useVar $ DBIndex $ theTyVar i
        (text x :) <$> do goArgument $ sequence $ map prettyPrecM $ theTyArgs as
      TLam f      -> lamParens $ do
        (mx, doc) <- goLambdaBody $ prettyAbs f
        let x = fromMaybe "_" mx
        return $ text ("λ " ++ x ++ " →") <+> doc
      TForall k f -> allParens $ do
        dk <- goForallDomain $ prettyPrecM k
        (mx, df) <- goForallBody $ prettyAbs f
        let x = fromMaybe "_" mx
        return $ text ("∀ " ++ x ++ " :") <+> dk <> text "." <+> df

    where
      appParens = parensIf appBrackets
      arrParens = parensIf arrowBrackets
      lamParens = parensIf lamBrackets
      allParens = parensIf forallBrackets

prettyAbs :: (Functor m, MonadName () m, PrettyM p m a) => I.Abs a -> m (Maybe Name, Doc)
prettyAbs (I.Abs   x a) = mapFst Just <$> do bindVar x __IMPOSSIBLE__ $ prettyPrecM a
prettyAbs (I.NoAbs x a) = (Nothing,) <$> prettyPrecM a

instance (Applicative m, Precedence p, MonadPrec p m, TypeRep m a) => PrettyM p m a where
  prettyPrecM a = prettyPrecM =<< typeView a
