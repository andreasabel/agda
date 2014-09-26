{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint
    ) where

import Data.Function
import Data.Int ( Int32 )
import Data.Monoid

import Text.PrettyPrint hiding (TextDetails(Str), empty)

import Agda.Utils.Null

instance Null Doc where
  empty = mempty
  null  = (== mempty)

-- * Pretty class

-- | While 'Show' is for rendering data in Haskell syntax,
--   'Pretty' is for displaying data to the world, i.e., the
--   user and the environment.
--
--   Atomic data has no inner document structure, so just
--   implement 'pretty' as @pretty a = text $ ... a ...@.

class Pretty a where
  pretty      :: a -> Doc
  prettyPrec  :: Int -> a -> Doc

  pretty      = prettyPrec 0
  prettyPrec  = const pretty

-- | Use instead of 'show' when printing to world.

prettyShow :: Pretty a => a -> String
prettyShow = render . pretty

-- * Pretty instances

instance Pretty Bool    where pretty = text . show
instance Pretty Int     where pretty = text . show
instance Pretty Int32   where pretty = text . show
instance Pretty Integer where pretty = text . show

instance Pretty Char where
  pretty c = text [c]

instance Pretty Doc where
  pretty = id

instance Pretty String where
  pretty = text

-- * Monadic pretty-printing

-- | Abstract type of precedences.

class TopPrecedence p where
  topPrecedence :: p
  -- ^ Top context precedence (usually lowest).

instance TopPrecedence () where
  topPrecedence = ()

instance TopPrecedence Int where
  topPrecedence = 0

-- | Abstract interface for monadic printing.

class (Monad m, TopPrecedence p) => MonadPretty p m a | a -> p where
  prettyM     :: a -> m Doc
  prettyPrecM :: p -> a -> m Doc

  prettyM     = prettyPrecM topPrecedence
  prettyPrecM = const prettyM

-- instance (Monad m, TopPrecedence p) => MonadPretty p m Doc where
--   prettyM = return

-- * 'Doc' utilities

#if !MIN_VERSION_pretty(1,1,2)
instance Eq Doc where
  (==) = (==) `on` render
#endif

pwords :: String -> [Doc]
pwords = map text . words

fwords :: String -> Doc
fwords = fsep . pwords

mparens :: Bool -> Doc -> Doc
mparens True  = parens
mparens False = id

-- | @align max rows@ lays out the elements of @rows@ in two columns,
-- with the second components aligned. The alignment column of the
-- second components is at most @max@ characters to the right of the
-- left-most column.
--
-- Precondition: @max > 0@.

align :: Int -> [(String, Doc)] -> Doc
align max rows =
  vcat $ map (\(s, d) -> text s $$ nest (maxLen + 1) d) $ rows
  where maxLen = maximum $ 0 : filter (< max) (map (length . fst) rows)
