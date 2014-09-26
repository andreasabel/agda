{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Pretty printer for Fω syntax

module Agda.Compiler.Fomega.Syntax.Pretty where

import Control.Applicative

import Agda.Compiler.Fomega.Syntax

import Agda.Utils.Pretty

-- * Symbols

dType, dTerm, dArrow, dForall, dLambda, dUnknown, dErased :: Doc
dType    = text "*"
dTerm    = text "()"
dArrow   = text "→" -- "->"
dForall  = text "∀" -- "forall"
dLambda  = text "λ" -- "\\"
dUnknown = text "?"
dErased  = text "()"

-- * Kinds

-- | Note: function space in domain @(k1 -> k2) -> k3@
--   vs. function space in range @k1 -> k2 -> k3@.
instance (Functor m, Applicative m, MonadPretty m a) => MonadPretty m (KindView' a) where
  prettyPrecM n k =
    case k of
      KType        -> return $ dType
      KTerm        -> return $ dTerm
      KArrow k1 k2 -> arr <$> prettyPrecM domPrec k1 <*> prettyPrecM rngPrec k2
        where
          arr d1 d2 = mparens inDom $ d1 <+> dArrow <+> d2
          inDom   = n >= domPrec
          domPrec = 1
          rngPrec = 0

-- Why does GHC-7.8.3 insist on an "Applicative m" constraint here?!
instance (Applicative m, KindRep m a) => MonadPretty m a where
  prettyPrecM n a = prettyPrecM n =<< kindView a

-- * Types

-- | Wrapper for pretty printing of variables.
newtype PrettyVar a = PrettyVar a

instance (MonadPretty m k, MonadPretty m a) => MonadPretty m (TypeView' k a) where
  prettyPrecM n a = do
    t <- typeView a
    case t of
      TUnknown   -> return $ dUnknown
      TErased    -> return $ dErased
      TArrow a b -> arrParens . fsep <$> sequence
        [ prettyPrecM domPrec a
        , return $ dArrow
        , prettyPrecM rngPrec b
        ]
      TCon c as  -> appParens . fsep . (pretty c :) <$> mapM (prettyPrecM argPrec) as
      TVar i as  -> appParens . fsep <$> do
        sequence $ prettyM (PrettyVar i) : map (prettyPrecM argPrec) as
    where
      argPrec = _
      domPrec = 1
      rngPrec = 0
      appParens = mparens $ n >= _
      arrParens = mparens $ n >= _

-- instance (MonadPretty k, PrettyTCM a) => PrettyTCM (TypeView' k a) where
--   prettyTCM
