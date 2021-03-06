{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}  -- Due to limitations of funct.dep.

-- | @ListT@ done right,
--   see https://www.haskell.org/haskellwiki/ListT_done_right_alternative
--
--   There is also the @list-t@ package on hackage (Nikita Volkov)
--   but it again depends on other packages we do not use yet,
--   so we rather implement the few bits we need afresh.

module Agda.Utils.ListT where

import Control.Applicative
import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans

import Data.Functor
import Data.Monoid

import Agda.Utils.Maybe
import Agda.Utils.Monad

-- | Lazy monadic computation of a list of results.
newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
  deriving (Functor)

-- * List operations

-- | The empty lazy list.
nilListT :: Monad m => ListT m a
nilListT = ListT $ return Nothing

-- | Consing a value to a lazy list.
consListT :: Monad m => a -> ListT m a -> ListT m a
consListT a l = ListT $ return $ Just (a, l)

-- | Singleton lazy list.
sgListT ::  Monad m => a -> ListT m a
sgListT a = consListT a nilListT

-- | Case distinction over lazy list.
caseListT :: Monad m => ListT m a -> m b -> (a -> ListT m a -> m b) -> m b
caseListT l nil cons = caseMaybeM (runListT l) nil $ uncurry cons

-- | Folding a lazy list, effects left-to-right.
foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT cons nil = loop where
  loop l = caseListT l nil $ \ a l' -> cons a $ loop l'

-- | The join operation of the @ListT m@ monad.
concatListT :: Monad m => ListT m (ListT m a) -> ListT m a
concatListT = ListT . foldListT append (return Nothing)
  where append l = runListT . mappend l . ListT

-- * Monadic list operations.

-- | We can ``run'' a computation of a 'ListT' as it is monadic itself.
runMListT :: Monad m => m (ListT m a) -> ListT m a
runMListT ml = ListT $ runListT =<< ml

-- | Monadic cons.
consMListT :: Monad m => m a -> ListT m a -> ListT m a
consMListT ma l = runMListT $ liftM (`consListT` l) ma

-- | Monadic singleton.
sgMListT ::  Monad m => m a -> ListT m a
sgMListT ma = consMListT ma nilListT

-- Instances

instance Monad m => Monoid (ListT m a) where
  mempty        = nilListT
  mappend l1 l2 = ListT $ foldListT cons (runListT l2) l1
    where cons a = runListT . consListT a . ListT

instance (Functor m, Applicative m, Monad m) => Alternative (ListT m) where
  empty = mempty
  (<|>) = mappend

instance (Functor m, Applicative m, Monad m) => MonadPlus (ListT m) where
  mzero = mempty
  mplus = mappend

instance (Functor m, Applicative m, Monad m) => Applicative (ListT m) where
  pure  = return
  (<*>) = ap

  -- Another Applicative, but not the canonical one.
  -- l1 <*> l2 = ListT $ loop <$> runListT l1 <*> runListT l2
  --   where
  --   loop (Just (f, l1')) (Just (a, l2')) = Just (f a, l1' <*> l2')
  --   loop _ _ = Nothing

instance (Functor m, Applicative m, Monad m) => Monad (ListT m) where
  return  = sgListT
  l >>= k = concatListT $ k <$> l

instance MonadTrans ListT where
  lift = sgMListT

instance (Applicative m, MonadIO m) => MonadIO (ListT m) where
  liftIO = lift . liftIO

instance (Applicative m, MonadReader r m) => MonadReader r (ListT m) where
  ask     = lift ask
  local f = ListT . local f . runListT

instance (Applicative m, MonadState s m) => MonadState s (ListT m) where
  get = lift get
  put = lift . put
