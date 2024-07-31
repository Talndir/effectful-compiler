{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Effect.Fresh where

import qualified Control.Monad.Trans.State.Strict as S

import Control.Effect
import Control.Family.Algebraic
import Control.Effect.State

type Fresh t = Alg (Fresh' t)
data Fresh' t a where
    Fresh :: (t -> a) -> Fresh' t a
    deriving Functor

fresh :: Member (Fresh t) sig => Prog sig t
fresh = call (Alg (Fresh return))

freshState :: (t -> t) -> Handler '[Fresh t] '[Put t, Get t] '[] '[]
freshState f = interpretM $ \oalg (Eff (Alg (Fresh k))) -> eval oalg $ do
    x <- get
    put (f x)
    return (k x)

freshH :: t -> (t -> t) -> Handler '[Fresh t] '[] '[S.StateT t] '[(,) t]
freshH init inc = freshState inc ||> state init

