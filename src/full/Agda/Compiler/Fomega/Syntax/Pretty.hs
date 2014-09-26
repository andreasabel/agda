-- {-# OPTIONS_GHC -fdefer-type-errors #-}
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

-- * Precedences

-- | Abstract specification of precedences.

class TopPrecedence p => Precedence p where
  goFunction     :: p -> p
  goArgument     :: p -> p
  goLambdaBody   :: p -> p
  goArrowDomain  :: p -> p
  goArrowRange   :: p -> p
  goForallDomain :: p -> p
  goForallBody   :: p -> p

  appBrackets    :: p -> Bool
  lamBrackets    :: p -> Bool
  arrowBrackets  :: p -> Bool
  forallBrackets :: p -> Bool

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

  goFunction     _ = FunctionPrec
  goArgument     p = ArgumentPrec   $ rightmost p
  goLambdaBody   _ = TopPrec
  goArrowDomain  _ = ArrowDomainPrec
  goArrowRange   p = ArrowRangePrec $ rightmost p
  goForallDomain _ = TopPrec
  goForallBody   _ = TopPrec

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
instance (Functor m, Applicative m, Monad m, Precedence p, PrettyM p m a) => PrettyM p m (KindView' a) where
  prettyPrecM k =
    case k of
      KType        -> pure $ dType
      KTerm        -> pure $ dTerm
      KArrow k1 k2 -> parensIf arrowBrackets $ do
         fsep <$> sequence
           [ localPrec goArrowDomain (prettyPrecM k1)
           , pure $ dArrow
           , localPrec goArrowRange  (prettyPrecM k2)
           ]

-- Why does GHC-7.8.3 insist on an "Applicative m" constraint here?!
instance (Applicative m, Precedence p, MonadPrec p m, KindRep m a) => PrettyM p m a where
  prettyPrecM a = prettyPrecM =<< kindView a

{-
-- * Types

instance MonadPretty m TyVar where

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
        sequence $ prettyM i : map (prettyPrecM argPrec) as
      TLam f      -> lamParens <$> prettyPrecM f
      TForall k f ->
    where
      argPrec = _
      domPrec = 1
      rngPrec = 0
      appParens = mparens $ n >= _
      arrParens = mparens $ n >= _
      lamParens = mparens $ n >= _

-- instance (MonadPretty k, PrettyTCM a) => PrettyTCM (TypeView' k a) where
--   prettyTCM
-- -}
