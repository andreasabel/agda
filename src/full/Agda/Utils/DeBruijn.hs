{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

-- | De Bruijn indices, levels, and contexts.

module Agda.Utils.DeBruijn where

import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IntMap
import           Data.Map      (Map)
import qualified Data.Map      as Map
import           Data.Maybe
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set      (Set)
import qualified Data.Set      as Set

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Size

-- * Context class

-- | De Bruijn indices.
newtype DBIndex = DBIndex { dbIndex :: Int }
  deriving (Eq, Ord, Show, Num)

-- | De Bruijn levels.
newtype DBLevel = DBLevel { dbLevel :: Int }
  deriving (Eq, Ord, Show, Num)

-- | Mapping indices/levels to something.
class Context c a | c -> a where

  lookupIndex  :: c -> DBIndex -> Maybe a
  lookupLevel  :: c -> DBLevel -> Maybe a

  indexToLevel :: c -> DBIndex -> DBLevel
  levelToIndex :: c -> DBLevel -> DBIndex

  ctxExtend    :: a -> c -> c
  ctxLength    :: c -> Int

  lookupIndex c = lookupLevel c . indexToLevel c
  lookupLevel c = lookupIndex c . levelToIndex c

  indexToLevel c (DBIndex i) = DBLevel $ ctxLength c - i - 1
  levelToIndex c (DBLevel l) = DBIndex $ ctxLength c - l - 1

-- * Instances

-- | Just the length of the context.
--
--   All operations: O(1).

instance Context Int () where
  lookupIndex c (DBIndex i)
    | i >= 0 && i < ctxLength c = Just ()
    | otherwise                 = Nothing
  ctxExtend _ = succ
  ctxLength   = id

-- | Context as plain list.
--
--   Lookup and length: O(n).
--   Extension: O(1).

instance Context [a] a where
  lookupIndex = (!!!) where
    []       !!! _ = Nothing
    (x : _)  !!! 0 = Just x
    (_ : xs) !!! n = xs !!! (n - 1)

  ctxLength = length
  ctxExtend = (:)

-- | List with precomputed length.
--
--   Invariant: @slSize == length . slList@
data SizedList a = SizedList { slSize :: !Int, slList :: [a] }

-- | Context as sized list.
--
--   Lookup   : O(n).
--   Length   : O(1).
--   Extension: O(1).

instance Context (SizedList a) a where
  lookupIndex                  = lookupIndex . slList
  ctxLength                    = slSize
  ctxExtend a (SizedList n as) = SizedList (n+1) (a:as)

-- | Context as plain 'IntMap' from de Bruijn levels to something.
--
--   Length   : O(n).
--   Extension: O(n), as it uses length.
--   Lookup   : O(log n).

instance Context (IntMap a) a where
  lookupLevel c (DBLevel l) = IntMap.lookup l c
  ctxLength                 = IntMap.size
  ctxExtend a c             = IntMap.insert (ctxLength c) a c

-- | IntMap with size field.

data SizedIntMap a = SizedIntMap { simSize :: !Int, simMap :: IntMap a }

-- | Context as sized 'IntMap' from de Bruijn levels to something.
--
--   Length   : O(1).
--   Extension: O(log n).
--   Lookup   : O(log n).

instance Context (SizedIntMap a) a where
  lookupLevel                   = lookupLevel . simMap
  ctxLength                     = simSize
  ctxExtend a (SizedIntMap n c) = SizedIntMap (n+1) $ IntMap.insert n a c

-- | Context as 'Data.Sequence'.
--
--   Lookup: O(log n).
--   Length: O(1).
--   Extend: O(1).

instance Context (Seq a) a where
  lookupIndex c (DBIndex i)
    | i >= 0 && i < ctxLength c = Just $ Seq.index c i
    | otherwise                 = Nothing
  ctxLength                     = Seq.length
  ctxExtend                     = (Seq.<|)

------------------------------------------------------------------------
-- * Null instances
------------------------------------------------------------------------

instance Null (SizedList a) where
  null  = (0 ==) . slSize
  empty = SizedList 0 []

instance Null (SizedIntMap a) where
  null  = (0 ==) . simSize
  empty = SizedIntMap 0 empty
