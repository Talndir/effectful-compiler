{-# LANGUAGE DataKinds #-}
module Effect.Unify where

import Control.Effect
import Control.Family.Algebraic
import Control.Effect.Except

type Unify f t = Alg (Unify' f t)
data Unify' f t a where
    Unify :: f t -> f t -> ((t -> f t) -> a) -> Unify' f t a

instance Functor (Unify' f t) where
    fmap f (Unify t1 t2 k) = Unify t1 t2 (f . k)

unify :: (Member (Unify f t) sig, Eq t) => f t -> f t -> Prog sig (t -> f t)
unify x y = call (Alg (Unify x y return))

unifyThrow :: (f t -> f t -> Prog '[Throw e] (t -> f t))
    -> Handler '[Unify f t] '[Throw e] '[] '[]
unifyThrow u = interpret $ \(Eff (Alg (Unify t1 t2 k))) -> do
    t <- u t1 t2
    return (k t)

aug :: Eq v => v -> t -> (v -> t) -> (v -> t)
aug v t f x
    | x == v = t
    | otherwise = f x

