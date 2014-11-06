module Agda.Utils.NameContext.Examples where

import Data.Maybe
import Data.Monoid

import Agda.Utils.NameContext
import Agda.Utils.Null
import Agda.Utils.Suffix

data Lam a = Var a | App (Lam a) (Lam a) | Abs String (Lam a)
  deriving Show

type Cxt       = SizedIntNameMap Name ()
type PrintM a  = Cxt -> (a, UsedNameSet)

name :: Lam DBIndex -> PrintM (Lam String)
name (Var i) gamma = (Var x, levelSingleton $ indexToLevel gamma i)
  where x = fst $ fromJust $ lookupIndex gamma i
name (App t u) gamma = (App t' u', mappend st su)
  where (t', st) = name t gamma
        (u', su) = name u gamma
name (Abs x t) gamma = (Abs x' t', ls)
  where (t', ls) = name t (ctxExtend (x',()) gamma)
        x'       = (`nameVariant` x) $ nameUsed gamma ls

-- type Name      = String
-- type Cxt       = [Name]
-- -- type UsedNames = Map Name Int  -- store the lowest DBLevel for a used Name
-- type PrintM a  = Cxt -> (a, UsedNames)

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

-- -- Variant with UsedNames = Set DBLevel

-- type UsedNames = Set Int

-- name :: Lam Int -> PrintM (Lam String)
-- name (Var i) gamma = (Var x, Set.singleton l)
--   where x = gamma !! i       -- Note:  i < length gamma
--         l = length gamma - i -- de Bruijn Level in [ 1 .. length gamma ]
--    --fromMaybe (error $ "unbound index " ++ show i) $
-- name (App t u) gamma = (App t' u', Set.union st su)
--   where (t', st) = name t gamma
--         (u', su) = name u gamma
-- name (Abs x t) gamma = (Abs x' t', ls)
--   where (t', ls) = name t (x':gamma)  -- ls in [ 1 .. length (x:gamma) ]
--         x'       = variant x (`Set.member` s)
--         s        = Set.fromList $ map (gamma !!) $ mapMaybe toIndex $ Set.toList ls
--         len      = length gamma
--         toIndex l = if l <= len then Just $ len - l else Nothing

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

doName t = fst $ name t empty

t0 = Abs "x" $ Var 0
t0' = doName t0

t1 = Abs "x" $ Abs "x" $ App (Var 0) (Var 1)
t1' = doName t1

t2 = Abs "x" $ App (Var 0) $ Abs "x" $  (Var 0)
t2' = doName t2

-- LOOPS:
--
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
