{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Effect.Map where

import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Effect.State
import qualified Data.Map as M

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped

import Effect.Modify

type Map k v = Alg (Map' k v)
data Map' k v a where
    Clear :: a -> Map' k v a
    Insert :: k -> v -> (Maybe v -> a) -> Map' k v a
    Delete :: k -> (Maybe v -> a) -> Map' k v a
    Lookup :: k -> (Maybe v -> a) -> Map' k v a
    Transform :: (v -> v) -> a -> Map' k v a
    deriving Functor

clear :: forall k v sig . Member (Map k v) sig => Prog sig ()
clear = call @(Map k v) (Alg (Clear (return ())))
insert :: Member (Map k v) sig => k -> v -> Prog sig (Maybe v)
insert k v = call (Alg (Insert k v return))
delete :: Member (Map k v) sig => k -> Prog sig (Maybe v)
delete k = call (Alg (Delete k return))
lookup :: Member (Map k v) sig => k -> Prog sig (Maybe v)
lookup k = call (Alg (Lookup k return))
transform :: forall k v sig . Member (Map k v) sig => (v -> v) -> Prog sig ()
transform f = call @(Map k v) (Alg (Transform f (return ())))

extend :: forall k v sig a . Member (Map k v) sig => k -> v -> Prog sig a -> Prog sig a
extend k v f = do
    v' <- lookup @k @v k
    insert k v
    r <- f
    case v' of
        Nothing -> delete k
        Just v'' -> insert k v''
    return r

mapAlg :: forall k v m . (Ord k, Monad m)
    => Algebra '[Put (M.Map k v), Get (M.Map k v)] m
    -> Algebra '[Map k v] m
mapAlg oalg (Eff (Alg op)) = eval oalg (g op) where
    g :: Map' k v x -> Prog '[Put (M.Map k v), Get (M.Map k v)] x
    g (Clear c) = put @(M.Map k v) M.empty >> return c
    g (Insert k v c) = do
        m <- get @(M.Map k v)
        let r = M.lookup k m
        put @(M.Map k v) (M.insert k v m)
        return (c r)
    g (Delete k c) = do
        m <- get @(M.Map k v)
        let r = M.lookup k m
        put @(M.Map k v) (M.delete k m)
        return (c r)
    g (Lookup k c) = do
        m <- get @(M.Map k v)
        return (c (M.lookup k m))
    g (Transform t c) = do
        m <- get @(M.Map k v)
        put @(M.Map k v) (M.map t m)
        return c

mapState :: forall k v . Ord k => Handler '[Map k v] '[Put (M.Map k v), Get (M.Map k v)] '[] '[]
mapState = interpretM mapAlg

mapModifyState :: forall k v . Ord k => Handler '[Map k v, Modify v] '[Put (M.Map k v), Get (M.Map k v)] '[] '[]
mapModifyState = interpretM (\oalg -> (mapAlg oalg) # (modifyAlg M.map oalg))

mapH :: forall k v . Ord k => Handler '[Map k v] '[] '[S.StateT (M.Map k v)] '[(,) (M.Map k v)]
mapH = mapState ||> state M.empty

mapMH :: forall k v . Ord k => Handler '[Map k v, Modify v] '[] '[S.StateT (M.Map k v)] '[(,) (M.Map k v)]
mapMH = mapModifyState ||> state M.empty
