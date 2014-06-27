module Term.Telescope
    ( -- * 'Tel'
      Tel(..)
    , ClosedTel
    , tel
    , unTel
    , idTel
    , proxyTel
    , substs
    , instantiate
    , (++)
      -- ** 'Tel' types
    , Proxy(..)
    , Id(..)
    , Prod2(..)
    , ProxyTel
    , ClosedProxyTel
    , IdTel
    , ClosedIdTel
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound                            hiding (instantiate)
import           Control.Applicative              ((<$>), (<*>), pure)
import           Control.Monad                    (liftM)
import           Data.Foldable                    (Foldable(foldMap))
import           Data.Monoid                      (mempty, (<>))
import           Data.Traversable                 (Traversable, sequenceA)
import           Data.Typeable                    (Typeable)
import           Data.Void                        (Void)

import           Syntax.Internal                  (Name)
import qualified Term.Context                     as Ctx
import           Term.Subst
import           Term.Var
import           Term.TermM

-- Tel
------------------------------------------------------------------------

-- | A 'Tel' is a list of types, each one ranging over the rest of the
-- list, and with something of at the end -- the inverse of a 'Ctx.Ctx',
-- plus the end element.
data Tel t f v
    = Empty (t f v)
    | Cons (Name, f v) (Tel t f (TermVar v))
    deriving (Functor, Typeable)

type ClosedTel t f = Tel t f Void

-- | Instantiates an 'IdTel' repeatedly until we get to the bottom of
-- it.  Fails If the length of the 'Tel' and the provided list don't
-- match.
substs :: (Subst f) => IdTel f v0 -> [f v0] -> TermM (f v0)
substs (Empty t)     []           = return $ unId t
substs (Empty _)     (_ : _)      = error "Types.Telescope.instantiate: too many arguments"
substs (Cons _ _)    []           = error "Types.Telescope.instantiate: too few arguments"
substs (Cons _ tel') (arg : args) = (`substs` args) =<< subst' tel' instArg
  where
    instArg (B _) = return arg
    instArg (F v) = return $ var v

-- | Instantiates a bound variable.
instantiate :: (Subst f, Subst' t) => Tel t f (TermVar v) -> f v -> TermM (Tel t f v)
instantiate tel' t = subst' tel' inst
  where
    inst (B _) = return t
    inst (F v) = return $ var v

-- Useful types
---------------

-- | A type with no data, useful to create 'Tel's with only types in
-- them.
data Proxy (f :: * -> *) v = Proxy

instance Functor (Proxy f) where
     fmap _ Proxy = Proxy

instance Foldable (Proxy f) where
     foldMap _ Proxy = mempty

instance Traversable (Proxy f) where
     sequenceA Proxy = pure Proxy

instance Bound Proxy where
     Proxy >>>= _ = Proxy

instance Subst' Proxy where
     subst' Proxy _ = return Proxy

-- | An identity type, useful to have terms at the end of a 'Tel'.
newtype Id f v = Id {unId :: f v}
  deriving (Functor, Foldable, Traversable)

instance Bound Id where
  Id t >>>= f = Id (t >>= f)

instance Subst' Id where
  subst' (Id t) f = Id <$> subst t f

data Prod2 (f :: * -> *) v = Prod2 (f v) (f v)
  deriving (Functor, Foldable, Traversable)

instance Bound Prod2 where
  Prod2 x y >>>= f = Prod2 (x >>= f) (y >>= f)

instance Subst' Prod2 where
  subst' (Prod2 x y) f = Prod2 <$> subst x f <*> subst y f

type IdTel    = Tel Id
type ProxyTel = Tel Proxy

type ClosedIdTel t    = IdTel t Void
type ClosedProxyTel t = ProxyTel t Void

-- Instances
----------------------

instance (Foldable f, Foldable (t f)) => Foldable (Tel t f) where
    foldMap f (Empty t)              = foldMap f t
    foldMap f (Cons (_, type_) tel') = foldMap f type_ <> foldMap f' tel'
      where
        f' (B _) = mempty
        f' (F v) = f v

instance (Traversable f, Traversable (t f)) => Traversable (Tel t f) where
    sequenceA (Empty t)              = Empty <$> sequenceA t
    sequenceA (Cons (n, type_) tel') = Cons <$> ((n ,) <$> sequenceA type_)
                                            <*> sequenceA (fmap sequenceA tel')

instance (Bound t) => Bound (Tel t) where
    (Empty t)              >>>= f = Empty (t >>>= f)
    (Cons (n, type_) tel') >>>= f = Cons (n, type_ >>= f) (tel' >>>= f')
      where
        f' (B v) = return (B v)
        f' (F v) = liftM F (f v)

instance (Subst' t) => Subst' (Tel t) where
    subst' (Empty t)              f = Empty <$> subst' t f
    subst' (Cons (n, type_) tel') f = Cons <$> ((n, ) <$> subst type_ f) <*> subst' tel' f'
      where
        f' (B v) = return $ var (B v)
        f' (F v) = substMap F =<< f v

-- To/from Ctx
--------------

tel :: Ctx.Ctx v0 f v -> t f v -> Tel t f v0
tel ctx0 t = go ctx0 (Empty t)
  where
    go :: Ctx.Ctx v0 f v -> Tel t f v -> Tel t f v0
    go Ctx.Empty            tel' = tel'
    go (Ctx.Snoc ctx type_) tel' = go ctx (Cons type_ tel')

idTel :: Ctx.Ctx v0 f v -> f v -> IdTel f v0
idTel ctx t = tel ctx (Id t)

proxyTel :: Ctx.Ctx v0 f v -> ProxyTel f v0
proxyTel ctx = tel ctx Proxy

unTel :: forall t f v0 a.
         (IsVar v0)
      => Tel t f v0
      -> (forall v. (IsVar v) => Ctx.Ctx v0 f v -> t f v -> a)
      -> a
unTel tel0 f = go tel0 Ctx.Empty
  where
    go :: (IsVar v) => Tel t f v -> Ctx.Ctx v0 f v -> a
    go (Empty t)         ctx = f ctx t
    go (Cons type_ tel') ctx = go tel' (Ctx.Snoc ctx type_)

(++) :: Ctx.Ctx v0 f v -> Tel t f v -> Tel t f v0
Ctx.Empty            ++ tel' = tel'
(Ctx.Snoc ctx type_) ++ tel' = ctx ++ (Cons type_ tel')
