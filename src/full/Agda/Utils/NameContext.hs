{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
class Context c n a | c -> a, c -> n where

  lookupIndex  :: c -> DBIndex -> Maybe (n, a)
  lookupLevel  :: c -> DBLevel -> Maybe (n, a)
  lookupNameLevels  :: Ord n => c -> n -> [DBLevel]
  lookupNameIndices :: Ord n => c -> n -> [DBIndex]

  indexToLevel :: c -> DBIndex -> DBLevel
  levelToIndex :: c -> DBLevel -> DBIndex

  ctxExtend    :: n -> a -> c -> c
  ctxLength    :: c -> Int

  lookupIndex c = lookupLevel c . indexToLevel c
  lookupLevel c = lookupIndex c . levelToIndex c

  lookupNameLevels  c = map (indexToLevel c) . lookupNameIndices c
  lookupNameIndices c = map (levelToIndex c) . lookupNameLevels  c

  indexToLevel c (DBIndex i) = DBLevel $ ctxLength c - i - 1
  levelToIndex c (DBLevel l) = DBIndex $ ctxLength c - l - 1

-- * Instances

-- | Context as association list from names to something.
--
--   Lookup and length: O(n).
--   Extension: O(1).

instance Context [(n,a)] n a where
  lookupIndex = (!!!) where
    []       !!! _ = Nothing
    (x : _)  !!! 0 = Just x
    (_ : xs) !!! n = xs !!! (n - 1)

  lookupNameIndices c n' =
    mapMaybe (\ (n,l) -> if  n==n' then Just l else Nothing) $
      zipWith (\ (n,_) l -> (n,l)) c [0..]

  ctxLength = length
  ctxExtend n a = ((n,a) :)

-- | List with precomputed length.
--
--   Invariant: @slSize == length . slList@
data SizedList a = SizedList { slSize :: !Int, slList :: [a] }

-- | Context as sized list.
--
--   Lookup   : O(n).
--   Length   : O(1).
--   Extension: O(1).

instance Context (SizedList (n,a)) n a where
  lookupIndex                    = lookupIndex . slList
  lookupNameIndices              = lookupNameIndices . slList
  ctxLength                      = slSize
  ctxExtend x a (SizedList n as) = SizedList (n+1) ((x,a):as)

-- | Context as plain 'IntMap' from de Bruijn levels to something.
--
--   Length   : O(n).
--   Extension: O(n), as it uses length.
--   Lookup   : O(log n).

instance Context (IntMap (n,a)) n a where
  lookupLevel c (DBLevel l) = IntMap.lookup l c
  lookupNameLevels c n'     =
    mapMaybe (\ (l,(n,_)) -> if n==n' then Just (DBLevel l) else Nothing) $
      IntMap.assocs c
  ctxLength                 = IntMap.size
  ctxExtend n a c           = IntMap.insert (ctxLength c) (n,a) c

-- | IntMap with size field.

data SizedIntMap a = SizedIntMap { simSize :: !Int, simMap :: IntMap a }

-- | Context as sized 'IntMap' from de Bruijn levels to something.
--
--   Length   : O(1).
--   Extension: O(log n).
--   Lookup   : O(log n).

instance Context (SizedIntMap (n,a)) n a where
  lookupLevel                     = lookupLevel . simMap
  lookupNameLevels                = lookupNameLevels . simMap
  ctxLength                       = simSize
  ctxExtend x a (SizedIntMap n c) = SizedIntMap (n+1) $ IntMap.insert n (x,a) c

-- | Context as 'Data.Sequence'.
--
--   Lookup: O(log n).
--   Length: O(1).
--   Extend: O(1).

instance Context (Seq (n,a)) n a where
  lookupIndex c (DBIndex i)
    | i >= 0 && i < ctxLength c = Just $ Seq.index c i
    | otherwise                 = Nothing
  lookupNameIndices             = lookupNameIndices . Fold.toList
  ctxLength                     = Seq.length
  ctxExtend n a                 = ((n,a) Seq.<|)


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

data IntNameMap n a = IntNameMap
  { intMap  :: IntMap (n,a)
  , nameMap :: Map n IntSet
  }

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
