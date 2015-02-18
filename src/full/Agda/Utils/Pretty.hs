{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-| Pretty printing functions.
-}
module Agda.Utils.Pretty
    ( module Agda.Utils.Pretty
    , module Text.PrettyPrint
    ) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer (Monoid,WriterT(..))
import Control.Monad.Trans

import Data.Function
import Data.Int ( Int32 )
import Data.Monoid hiding ((<>))

import Text.PrettyPrint hiding (TextDetails(Str), empty)

import Agda.Utils.Functor
import Agda.Utils.Monad
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

-- ** Top precedence

-- | Abstract type of precedences.

class TopPrecedence p where
  topPrecedence :: p
  -- ^ Top context precedence (usually lowest).

instance TopPrecedence () where
  topPrecedence = ()

instance TopPrecedence Int where
  topPrecedence = 0

-- ** Precedence reader

-- | Precedence context monad.  A copy of 'MonadReader'.

class Monad m => MonadPrec p m | m -> p where
  askPrec   :: m p
  localPrec :: (p -> p) -> m a -> m a

-- The functional dependency requires UndecidableInstances:
-- Apparently m -> p does not imply ReaderT r m -> p.
instance MonadPrec p m => MonadPrec p (ReaderT r m) where
  askPrec = lift $ askPrec
  localPrec f (ReaderT m) = ReaderT $ \ r -> localPrec f (m r)

instance (MonadPrec p m, Monoid w) => MonadPrec p (WriterT w m) where
  askPrec = lift $ askPrec
  localPrec f (WriterT m) = WriterT $ localPrec f m

-- | Continue in top context.
inTopPrec :: (TopPrecedence p, MonadPrec p m) => m a -> m a
inTopPrec = localPrec $ const topPrecedence

-- -- | No precedence information.
-- instance Monad m => MonadPrec () m where
--   askPrec   = return ()
--   localPrec = const id

-- | Precedence monad transformer.
newtype PrecT p m a = PrecT { unPrecT :: ReaderT p m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadFix)

instance Monad m => MonadPrec p (PrecT p m) where
  askPrec = PrecT $ ask
  localPrec f (PrecT m) = PrecT $ local f m

-- instance MonadFix m => MonadFix (PrecT p m) where
--   -- mfix :: (a -> PrecT p m a) -> PrecT p m a
--   mfix f = PrecT $ mfix (unPrecT . f)

-- | Running precedence-reading computation.
runPrecT' :: PrecT p m a -> p -> m a
runPrecT' = runReaderT . unPrecT

-- | Running computation with default precedence.
runPrecT :: TopPrecedence p => PrecT p m a -> m a
runPrecT = (`runPrecT'` topPrecedence)

-- | Abstract interface for monadic printing.

class MonadPrec p m => PrettyM p m a where
  prettyPrecM :: a -> m Doc

instance (Applicative m, MonadPrec p m) => PrettyM p m Doc where
  prettyPrecM = pure

-- | Print something in delimiters if some condition holds.
bracketIf :: (TopPrecedence p, Functor m, Monad m, MonadPrec p m)
  => Doc          -- ^ Opening bracket.
  -> Doc          -- ^ Closing bracket.
  -> (p -> Bool)  -- ^ Condition on precedence whether to bracket.
  -> m Doc        -- ^ Inner computation, run in top context if bracketing.
  -> m Doc        -- ^ Result is bracketed if condition held.
bracketIf open close test cont =
  -- If test fails on precedence, just continue.
  ifNotM (test <$> askPrec) cont $ {- else -}
  -- Other wise, continue in top context, and wrap result in delimiters.
  inTopPrec cont <&> \ d -> open <> d <> close

-- | Print something in parentheses if some condition holds.
parensIf ::  (TopPrecedence p, Functor m, Monad m, MonadPrec p m)
  => (p -> Bool)  -- ^ Condition on precedence whether to parenthesize.
  -> m Doc        -- ^ Inner computation, run in top context if parenthesizing.
  -> m Doc        -- ^ Result is parenthesized if condition held.
parensIf = bracketIf lparen rparen

-- Needs {-# LANGUAGE AllowAmbiguousTypes #-}
-- prettyM :: (TopPrecedence p, PrettyM p (PrecT p m) a) => a -> m Doc
-- prettyM = runPrecT . prettyPrecM

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
