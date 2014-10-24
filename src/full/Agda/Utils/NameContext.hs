{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Infrastructure for picking names for binders.

module Agda.Utils.NameContext where

import qualified Data.Foldable as Fold
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set


import Agda.Utils.Functor
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

-- * Context class

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

-- * Instances

-- | Requires @UndecidableInstances@ due to a weakness of
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
--   Lookup and length: O(n).
--   Extension  : O(1).
--   Name lookup: O(n)

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
type SizedList a = SizedThing [a]

-- -- | List with precomputed length.
-- --
-- --   Invariant: @slSize == length . slList@
-- data SizedList a = SizedList { slSize :: !Int, slList :: [a] }
--
-- -- | Context as sized list.
-- --
-- --   Lookup     : O(n).
-- --   Length     : O(1).
-- --   Extension  : O(1).
-- --   Name lookup: O(n)
--
-- instance Context (SizedList (n,a)) n a where
--   lookupIndex                    = lookupIndex . slList
--   lookupNameIndices              = lookupNameIndices . slList
--   ctxLength                      = slSize
--   ctxExtend na (SizedList len as) = SizedList (len+1) (na:as)
--
-- | Context as plain 'IntMap' from de Bruijn levels to something.
--
--   Length     : O(n).
--   Extension  : O(n), as it uses length.
--   Lookup     : O(log n).
--   Name lookup: O(n)

instance Context (IntMap (n,a)) n a where
  lookupLevel c (DBLevel l) = IntMap.lookup l c
  lookupNameLevels c n'     =
    mapMaybe (\ (l,(n,_)) -> if n==n' then Just (DBLevel l) else Nothing) $
      IntMap.assocs c
  ctxLength                 = IntMap.size
  ctxSizedExtend na (SizedThing len c) = IntMap.insert len na c

-- | IntMap with size field.

type SizedIntMap a = SizedThing (IntMap a)

-- data SizedIntMap a = SizedIntMap { simSize :: !Int, simMap :: IntMap a }

-- -- | Context as sized 'IntMap' from de Bruijn levels to something.
-- --
-- --   Length     : O(1).
-- --   Extension  : O(log n).
-- --   Lookup     : O(log n).
-- --   Name lookup: O(n)

-- instance Context (SizedIntMap (n,a)) n a where
--   lookupLevel                      = lookupLevel . simMap
--   lookupNameLevels                 = lookupNameLevels . simMap
--   ctxLength                        = simSize
--   ctxExtend na (SizedIntMap len c) = SizedIntMap (len+1) $ IntMap.insert len na c

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


data IntNameMap n a = IntNameMap
  { intMap  :: IntMap (n,a)
  , nameMap :: Map n IntSet
  }

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

type SizedIntNameMap n a = SizedThing (IntNameMap n a)

-- data SizedIntNameMap n a = SizedIntNameMap
--   { sinSize :: !Int
--   , sinMap  :: IntNameMap n a
--   }

-- instance Ord n => Context (SizedIntNameMap n a) n a where
--   lookupLevel                        = lookupLevel . sinMap
--   lookupNameLevels                   = lookupNameLevels . sinMap
--   ctxLength                          = sinSize
--   ctxExtend na (SizedIntNameMap l m) = SizedIntNameMap (l+1) $
--     ctxSizedExtend na (l, m)

-- | Context as bimap.

class Null l => LevelCollection l where
  levelMember :: DBLevel -> l -> Bool
  levelInsert :: DBLevel -> l -> l

--
instance Null DBLevel where
  null  = (< 0)
  empty = 0 - 1

instance LevelCollection DBLevel where
  levelMember = (<=)
  levelInsert = max


-- | Variables are represented as de Bruijn indices.
type Var = Int

-- | Predicate 'MayShadow' indicates which de Bruijn indices
--   can be ignored when a new name conflicts with an old name.
type MayShadow = Var -> Bool

class NameContext c where
  nameOf :: c -> Var -> String
  addName :: String -> c -> c


data Lam a = Var a | App (Lam a) (Lam a) | Abs String (Lam a)
  deriving Show

type Name      = String
type Cxt       = [Name]
-- type UsedNames = Map Name Int  -- store the lowest DBLevel for a used Name
type PrintM a  = Cxt -> (a, UsedNames)

-- -- Variant with UsedNames = Set DBLevel

-- name :: Lam Int -> PrintM (Lam Name)
-- name (Var i) gamma = (Var x, Map.singleton x l)
--   where x = gamma !! i       -- Note:  i < length gamma
--         l = length gamma - i -- de Bruijn Level in [ 1 .. length gamma ]
--    --fromMaybe (error $ "unbound index " ++ show i) $
-- name (App t u) gamma = (App t' u', Map.unionWith min st su)
--   where (t', st) = name t gamma
--         (u', su) = name u gamma
-- name (Abs x t) gamma = (Abs x' t', ls)
--   where (t', ls) = name t (x':gamma)  -- ls in [ 1 .. length (x:gamma) ]
--         x'       = variant x used
--         used y   = caseMaybe (Map.lookup y ls) False (< length gamma)
--         -- NON-TERMINATING (BAD CYCLE)

variant :: Name -> (Name -> Bool) -> Name
variant x used = addSuffix x $ loop $ Prime 0
  where
    loop s = if used x' then loop (nextSuffix s) else s
      where x' = addSuffix x s

-- Variant with UsedNames = Set DBLevel

type UsedNames = Set Int

name :: Lam Int -> PrintM (Lam String)
name (Var i) gamma = (Var x, Set.singleton l)
  where x = gamma !! i       -- Note:  i < length gamma
        l = length gamma - i -- de Bruijn Level in [ 1 .. length gamma ]
   --fromMaybe (error $ "unbound index " ++ show i) $
name (App t u) gamma = (App t' u', Set.union st su)
  where (t', st) = name t gamma
        (u', su) = name u gamma
name (Abs x t) gamma = (Abs x' t', ls)
  where (t', ls) = name t (x':gamma)  -- ls in [ 1 .. length (x:gamma) ]
        x'       = variant x (`Set.member` s)
        s        = Set.fromList $ map (gamma !!) $ mapMaybe toIndex $ Set.toList ls
        len      = length gamma
        toIndex l = if l <= len then Just $ len - l else Nothing

-- Variant with UsedNames = Set DBIndex

-- type UsedNames = Set Int

-- name :: Lam Int -> PrintM (Lam String)
-- name (Var i) gamma = (Var x, Set.singleton i)
--   where x = gamma !! i
--         l = length gamma - i
--    --fromMaybe (error $ "unbound index " ++ show i) $
-- name (App t u) gamma = (App t' u', Set.union st su)
--   where (t', st) = name t gamma
--         (u', su) = name u gamma
-- name (Abs x t) gamma = (Abs x' t', is')
--   where (t', is) = name t (x':gamma)
--         is'      = Set.mapMonotonic (\ x -> x - 1) $ Set.delete 0 is
--         s        = Set.map (gamma !!) is'
--         x'       = variant x s

-- variant :: String -> Set String -> String
-- variant x used = addSuffix x $ loop $ Prime 0
--   where
--     loop s = if x' `Set.member` used then loop (nextSuffix s) else s
--       where x' = addSuffix x s

doName t = fst $ name t []

t0 = Abs "x" $ Var 0
t0' = doName t0

t1 = Abs "x" $ Abs "x" $ App (Var 0) (Var 1)
t1' = doName t1

t2 = Abs "x" $ App (Var 0) $ Abs "x" $  (Var 0)
t2' = doName t2

-- type Cxt       = [String]
-- type UsedNames = Set String
-- type PrintM a  = Cxt -> (a, UsedNames)

-- name :: Lam Int -> PrintM (Lam String)
-- name (Var i) gamma = (Var x, Set.singleton x)
--   where x = gamma !! i
--    --fromMaybe (error $ "unbound index " ++ show i) $
-- name (App t u) gamma = (App t' u', Set.union st su)
--   where (t', st) = name t gamma
--         (u', su) = name u gamma
-- name (Abs x t) gamma = (Abs x' t', s)
--   where (t', s) = name t (x':gamma)
--         x'      = variant x s

-- variant :: String -> Set String -> String
-- variant x used = addSuffix x $ loop NoSuffix
--   where
--     loop s = if x' `Set.member` used then loop (nextSuffix s) else s
--       where x' = addSuffix x s

-- doName t = fst $ name t []

-- t0 = Abs "x" $ Var 0
-- t0' = doName t0

-- t1 = Abs "x" $ Abs "x" $ App (Var 0) (Var 1)
-- t1' = doName t1
