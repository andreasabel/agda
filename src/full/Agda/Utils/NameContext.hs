{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Infrastructure for picking names for binders.

module Agda.Utils.NameContext where

import Prelude hiding (null)

import qualified Data.Foldable as Fold
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set


import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Suffix


-- | De Bruijn indices.
newtype DBIndex = DBIndex { dbIndex :: Int }
  deriving (Eq, Ord, Show, Num, Enum)

-- | De Bruijn levels.
newtype DBLevel = DBLevel { dbLevel :: Int }
  deriving (Eq, Ord, Show, Num, Enum)

------------------------------------------------------------------------
-- * Context carrying variable name suggestions (and other information)
------------------------------------------------------------------------

-- ** Context class

-- | Mapping indices/levels to a name and something else.
--   Supports efficient reverse lookup for names.
--
--   Names are not unique, they can be shadowed.
class Sized c => Context c n a | c -> a, c -> n where

  lookupIndex  :: c -> DBIndex -> Maybe (n, a)
  lookupLevel  :: c -> DBLevel -> Maybe (n, a)

  -- | Get all the bindings that use a specific name.
  --   Assumption: only a few bindings share the same name,
  --   thus, the returned list is short.
  lookupNameLevels  :: Ord n => c -> n -> [DBLevel]
  lookupNameIndices :: Ord n => c -> n -> [DBIndex]

  ctxExtend    :: (n, a) -> c -> c
  ctxLength    :: c -> Int

  -- | Optimized version of ctxExtend if we have the length of the context already.
  ctxSizedExtend :: (n, a) -> SizedThing c -> c

  -- default implementations

  lookupIndex c = lookupLevel c . indexToLevel c
  lookupLevel c = lookupIndex c . levelToIndex c

  lookupNameLevels  c = map (indexToLevel c) . lookupNameIndices c
  lookupNameIndices c = map (levelToIndex c) . lookupNameLevels  c

  ctxLength = size

  ctxExtend na c = ctxSizedExtend na $ sizeThing c
  ctxSizedExtend na c = ctxExtend na $ sizedThing c

indexToLevel :: Context c n a => c -> DBIndex -> DBLevel
indexToLevel c (DBIndex i) = DBLevel $ ctxLength c - i - 1

levelToIndex :: Context c n a => c -> DBLevel -> DBIndex
levelToIndex c (DBLevel l) = DBIndex $ ctxLength c - l - 1

-- ** Instances

-- | Use the cached size as 'ctxLength' to speed up
--   every operation relying on 'ctxLength',
--   reducing complexity from linear to constant or logarithmic.
--
--   Note: Requires @UndecidableInstances@ due to a weakness of
--   @FunctionalDependencies@.
--   One would expect that if @c@ determines @n@ and @a@,
--   so does @SizedThing c@ (which is actually @(Int,c)@).
--   But GHC fails to see this.

instance (Context c n a) => Context (SizedThing c) n a where
  lookupIndex = lookupIndex . sizedThing
  lookupLevel = lookupLevel . sizedThing

  lookupNameLevels  = lookupNameLevels  . sizedThing
  lookupNameIndices = lookupNameIndices . sizedThing

  ctxLength    = theSize
  ctxExtend na c = SizedThing (theSize c + 1) $ ctxSizedExtend na c


-- | Context as association list from names to something.
--
--   Lookup     : O(n).
--   Length     : O(n).
--   Extension  : O(1).
--   Name lookup: O(n).

instance Context [(n,a)] n a where
  lookupIndex = (!!!) where
    []       !!! _ = Nothing
    (x : _)  !!! 0 = Just x
    (_ : xs) !!! i = xs !!! (i - 1)

  lookupNameIndices c n' =
    mapMaybe (\ (n,i) -> if  n==n' then Just i else Nothing) $
      zipWith (\ (n,_) i -> (n,i)) c [0..]  -- last binding is first, index 0

  ctxLength = length
  ctxExtend = (:)

-- | List with precomputed length.
--
--   Context operations:
--   Lookup     : O(n).
--   Length     : O(1).
--   Extend     : O(1).
--   Name lookup: O(n).

type SizedList a = SizedThing [a]

-- | Context as plain 'IntMap' from de Bruijn levels to something.
--
--   Lookup     : O(log n).
--   Length     : O(n).
--   Extend     : O(n), as it uses length.
--   Name lookup: O(n)

instance Context (IntMap (n,a)) n a where
  lookupLevel c (DBLevel l) = IntMap.lookup l c
  lookupNameLevels c n'     =
    mapMaybe (\ (l,(n,_)) -> if n==n' then Just (DBLevel l) else Nothing) $
      IntMap.assocs c
  ctxLength                 = IntMap.size
  ctxSizedExtend na (SizedThing len c) = IntMap.insert len na c

-- | IntMap with size field.
--
--   Context operations:
--   Lookup     : O(log n).
--   Length     : O(1).
--   Extend     : O(log n).
--   Name lookup: O(n)

type SizedIntMap a = SizedThing (IntMap a)

-- | Context as 'Data.Sequence'.
--
--   Lookup     : O(log n).
--   Length     : O(1).
--   Extend     : O(1).
--   Name lookup: O(n)

instance Context (Seq (n,a)) n a where
  lookupIndex c (DBIndex i)
    | i >= 0 && i < ctxLength c = Just $ Seq.index c i
    | otherwise                 = Nothing
  lookupNameIndices             = lookupNameIndices . Fold.toList
  ctxLength                     = Seq.length
  ctxExtend                     = (Seq.<|)


-- | Context as 'IntMap' from de Bruijn levels to something,
--   combined with a 'Map' from names to de Bruijn levels.
--
--   Lookup     : O(log n).
--   Length     : O(n).
--   Extend     : O(n), as it uses length.
--   Name lookup: O(log n).

data IntNameMap n a = IntNameMap
  { intMap  :: IntMap (n,a)
  , nameMap :: Map n IntSet
  }

instance Null (IntNameMap n a) where
  empty = IntNameMap empty empty
  null  = null . intMap

instance Sized (IntNameMap n a) where
  size = size . intMap

instance Ord n => Context (IntNameMap n a) n a where
  lookupLevel                           = lookupLevel . intMap
  lookupNameLevels c n                  =
    maybe [] (map DBLevel . IntSet.toList) $ Map.lookup n (nameMap c)
  ctxLength                             = ctxLength . intMap
  ctxSizedExtend na@(n,_) (SizedThing l (IntNameMap im nm)) = IntNameMap
    { intMap  = ctxExtend na im
    , nameMap = Map.alter (maybe (Just $ IntSet.singleton l) (Just . IntSet.insert l)) n nm
    }

-- | Context as 'IntMap' from de Bruijn levels to something,
--   combined with a 'Map' from names to de Bruijn levels;
--   length of context is cached.
--
--   Lookup     : O(log n).
--   Length     : O(1).
--   Extend     : O(1).
--   Name lookup: O(log n).

type SizedIntNameMap n a = SizedThing (IntNameMap n a)


------------------------------------------------------------------------
-- * Structure to collect used names in an expression
------------------------------------------------------------------------

-- | Concrete names for printing variables and definitions.
type Name = String

-- ** UsedNames class

-- | Collect used names (from defined things) and de Bruijn levels
--   (free variables).

class (Null u, Monoid u) => UsedNames u where
  levelInsert :: DBLevel -> u -> u
  nameInsert  :: Name -> u -> u

  levelMember :: DBLevel -> u -> Bool
  nameMember  :: Name -> u -> Bool

  setOfUsedNames :: (DBLevel -> Name) -> u -> Set Name

levelSingleton :: (UsedNames u) => DBLevel -> u
levelSingleton l = levelInsert l empty

-- ** UsedNames instance

-- | Implementation of 'UsedNames' by a pair of sets.
data UsedNameSet = UsedNameSet
  { _usedLevels :: Set DBLevel
  , _usedNames  :: Set Name
  }

-- | Lens for '_usedLevels'.
usedLevels :: Lens' (Set DBLevel) UsedNameSet
usedLevels f o = f (_usedLevels o) <&> \ i -> o { _usedLevels = i }

-- | Lens for '_usedNames'.
usedNames :: Lens' (Set Name) UsedNameSet
usedNames f o = f (_usedNames o) <&> \ i -> o { _usedNames = i }

instance Null UsedNameSet where
  empty  = UsedNameSet empty empty
  null u = null (u ^. usedLevels) && null (u ^. usedNames)

instance Monoid UsedNameSet where
  mempty = empty
  mappend (UsedNameSet ls ns) (UsedNameSet ls' ns') =
    UsedNameSet (mappend ls ls') (mappend ns ns')

instance UsedNames UsedNameSet where
  levelInsert l = over usedLevels $ Set.insert l
  nameInsert x  = over usedNames  $ Set.insert x

  levelMember l u = Set.member l $ u ^. usedLevels
  nameMember x  u = Set.member x $ u ^. usedNames

  setOfUsedNames f u = Set.map f (u ^. usedLevels) `mappend` (u ^. usedNames)


-- * Fresh name generation tools for printing in a name Context.

-- | In a given context and set of levels and names mentioned in an expression,
--   check whether a name is taken.
nameUsed :: (Context c Name a, UsedNames u) => c -> u -> Name -> Bool
nameUsed c u x = x `nameMember` u
  || any (`levelMember` u)
         (filter ((<= ctxLength c) . dbLevel) $ lookupNameLevels c x)
