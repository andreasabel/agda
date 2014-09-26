{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Pretty printer for Fω syntax

module Agda.Compiler.Fomega.Syntax.Pretty where

import Control.Applicative

import Agda.Compiler.Fomega.Syntax

import Agda.Utils.Pretty

-- * Kinds

-- | Note: function space in domain @(k1 -> k2) -> k3@
--   vs. function space in range @k1 -> k2 -> k3@.
instance (Functor m, Applicative m, MonadPretty m a) => MonadPretty m (KindView' a) where
  prettyPrecM n k =
    case k of
      KType        -> return $ text "*"
      KTerm        -> return $ text "()"
      KArrow k1 k2 -> arr <$> prettyPrecM domPrec k1 <*> prettyPrecM rngPrec k2
        where
          arr d1 d2 = mparens inDom $ d1 <+> text "->" <+> d2
          inDom   = n >= domPrec
          domPrec = 1
          rngPrec = 0

-- Why does GHC-7.8.3 insist on an "Applicative m" constraint here?!
instance (Applicative m, KindRep m a) => MonadPretty m a where
  prettyPrecM n a = prettyPrecM n =<< kindView a
