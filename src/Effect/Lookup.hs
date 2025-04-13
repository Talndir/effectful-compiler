{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Effect.Lookup where

import Prelude hiding (lookup)
import qualified Data.Map as M

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.State
import Control.Effect.Except

import Effect.Modify


type Lookup v t = Alg (Lookup' v t)
data Lookup' v t a where
    Lookup :: v -> (t -> a) -> Lookup' v t a
    deriving Functor

lookup :: Member (Lookup v t) sig => v -> Prog sig t
lookup v = call (Alg (Lookup v return))

type Extend v t = Scp (Extend' v t)
data Extend' v t a where
    Extend :: v -> t -> a -> Extend' v t a
    deriving Functor

extend :: Member (Extend v t) sig => v -> t -> Prog sig a -> Prog sig a
extend v t p = call (Scp (Extend v t (fmap return p)))

type Contains t = Alg (Contains' t)
data Contains' t a where
    Contains :: t -> (Bool -> a) -> Contains' t a
    deriving Functor

contains :: Member (Contains t) sig => t -> Prog sig Bool
contains t = call (Alg (Contains t return))

type Update v t = Alg (Update' v t)
data Update' v t a where
    Update :: v -> t -> a -> Update' v t a
    deriving Functor

update :: Member (Update v t) sig => v -> t -> Prog sig ()
update v t = call (Alg (Update v t (return ())))


lookupMapAlg :: forall k v m effs . (Ord k, Monad m, Members '[Get (M.Map k v), Throw String] effs)
    => Algebra effs m
    -> Algebra '[Lookup k v] m
lookupMapAlg oalg (Eff (Alg (Lookup k p))) = eval oalg $ do
    m <- get @(M.Map k v)
    case M.lookup k m of
        Just v -> return (p v)
        Nothing -> throw "Error: Failed lookup"

extendMapAlg :: forall k v m effs . (Ord k, Monad m, Members '[Put (M.Map k v), Get (M.Map k v)] effs)
    => Algebra effs m
    -> Algebra '[Extend k v] m
extendMapAlg oalg (Eff (Scp (Extend k v p))) = do
    m <- eval oalg $ do
        m <- get
        put (M.insert k v m)
        return m
    x <- p
    eval oalg $ put m
    return x

containsMapAlg :: forall k v m effs . (Monad m, Eq v, Members '[Get (M.Map k v)] effs)
    => Algebra effs m
    -> Algebra '[Contains v] m
containsMapAlg oalg (Eff (Alg (Contains v p))) = eval oalg $ do
    m <- get @(M.Map k v)
    return (p (v `elem` M.elems m))

containsMapInnerAlg :: forall f k v m effs . (Monad m, Eq v, Foldable f, Members '[Get (M.Map k (f v))] effs)
    => Algebra effs m
    -> Algebra '[Contains v] m
containsMapInnerAlg oalg (Eff (Alg (Contains v p))) = eval oalg $ do
    m <- get @(M.Map k (f v))
    return . p . not . null . filter (v `elem`) . M.elems $ m

updateMapAlg :: forall k v m effs . (Monad m, Ord k, Members [Put (M.Map k v), Get (M.Map k v)] effs)
    => Algebra effs m
    -> Algebra '[Update k v] m
updateMapAlg oalg (Eff (Alg (Update k v p))) = eval oalg $ do
    m <- get
    put (M.insert k v m)
    return p

contextState :: forall v f t . Handler [Lookup v (f t), Modify (v -> f t)] '[Put (v -> f t), Get (v -> f t)] '[] '[]
contextState = interpretM f where
    f :: Monad m => (forall x. Effs '[Put (v -> f t), Get (v -> f t)] m x -> m x)
        -> forall x. Effs '[Lookup v (f t), Modify (v -> f t)] m x -> m x
    f oalg op
        | Just (Alg (Lookup v k)) <- prj @(Lookup v (f t)) op = eval oalg $ do
            w <- get
            return (k (w v))
        | Just (Scp (Modify g k)) <- prj @(Modify (v -> f t)) op = do
            w <- eval oalg $ do
                w <- get @(v -> f t)
                put (g w)
                return w
            x <- k
            eval oalg (put w)
            return x
        | otherwise = undefined


contextMap :: forall v t f . (Ord v, Eq t, Foldable f)
    => Handler [Lookup v (f t), Contains t, Modify (f t), Extend v (f t)]
              '[Put (M.Map v (f t)), Get (M.Map v (f t)), Throw String]
              '[] '[]
contextMap = interpretM $ \oalg
    -> lookupMapAlg oalg
    #  containsMapInnerAlg @f @v oalg
    #  modifyAlg @_ @(M.Map v (f t)) M.map oalg
    #  extendMapAlg @v @(f t) oalg
