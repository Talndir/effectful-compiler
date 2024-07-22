{-# LANGUAGE DataKinds #-}
module Typing.Typer1 where

import Control.Monad.Trans.State.Strict (StateT(..))

import Control.Effect
import Control.Family.Algebraic
import Control.Effect.State

import Language.Lambda1

type Fresh t = Alg (Fresh' t)
data Fresh' t a where
    Fresh :: (t -> a) -> Fresh' t a
    deriving Functor

freshState :: (t -> t) -> Handler '[Fresh t] '[Put t, Get t] '[] '[]
freshState f = interpretM $ \oalg (Eff (Alg (Fresh k))) -> eval oalg $ do
    x <- get
    put (f x)
    return (k x)

type Unify t = Alg (Unify' t)
data Unify' t a where
    Unify :: t -> t -> (t -> a) -> Unify' t a
    deriving Functor

unifyFresh :: (t -> t -> Prog '[Fresh t] t) -> Handler '[Unify t] '[Fresh t] '[] '[]
unifyFresh f = interpretM $ \oalg (Eff (Alg (Unify t1 t2 k))) -> eval oalg $ do
    t <- f t1 t2
    return (k t)

typer :: t -> (t -> t -> Prog '[Fresh t] t) -> (t -> t)
      -> Handler '[Unify t, Fresh t] '[] '[StateT t] '[(,) t]
typer s u f = unifyFresh u |> freshState f `pipe` state s

type Map k v = Alg (Map' k v)
data Map' k v a where
    Clear :: Map' k v ()
    Insert :: k -> v -> Map' k v (Maybe v)
    Delete :: k -> Map' k v (Maybe v)
    Lookup :: k -> Map' k v (Maybe v)
    Transform :: (v -> v) -> Map' k v ()
