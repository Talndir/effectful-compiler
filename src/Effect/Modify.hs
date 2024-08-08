{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Effect.Modify where

import Control.Effect
import Control.Family.Scoped

import Control.Effect.State

type Modify t = Scp (Modify' t)
data Modify' t a where
    Modify :: (t -> t) -> a -> Modify' t a
    deriving Functor

modify :: forall t sig a . Member (Modify t) sig => (t -> t) -> Prog sig a -> Prog sig a
modify f k = call @(Modify t) (Scp (Modify f (fmap return k)))

modifyAlg :: forall t s m effs . (Monad m, Members '[Put s, Get s] effs)
    => ((t -> t) -> (s -> s))
    -> Algebra effs m
    -> Algebra '[Modify t] m
modifyAlg t oalg (Eff (Scp (Modify f k))) =do
    s <- eval oalg $ do
        s <- get @s
        put (t f s)
        return s
    x <- k
    eval oalg $ put @s s
    return x
