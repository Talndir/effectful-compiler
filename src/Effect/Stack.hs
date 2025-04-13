{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Effect.Stack where

import qualified Control.Monad.Trans.State.Strict as S

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.State

data Push' s a = Push s a deriving Functor
type Push s = Alg (Push' s)

data Pop' s a = Pop (Maybe s -> a) deriving Functor
type Pop s = Alg (Pop' s)

data With' s a = With ([s] -> s) a deriving Functor
type With s = Scp (With' s)

push :: Member (Push s) sig => s -> Prog sig ()
push x = call (Alg (Push x (return ())))

pop :: Member (Pop s) sig => Prog sig (Maybe s)
pop = call (Alg (Pop return))

with :: Member (With s) sig => ([s] -> s) -> Prog sig a -> Prog sig a
with f p = call (Scp (With f (fmap return p)))

extra :: forall s sig a . Members [Push s, Pop s] sig => s -> Prog sig a -> Prog sig a
extra x p = do
    push x
    r <- p
    pop @s
    return r

pushPopState :: forall s . Handler '[Push s, Pop s] '[Put [s], Get [s]] '[] '[]
pushPopState = interpretM f where
    f :: Monad m => Algebra [Put [s], Get [s]] m -> Algebra [Push s, Pop s] m
    f oalg op
        | Just (Alg (Push x k)) <- prj @(Push s) op = eval oalg $ do
            xs <- get
            put (x : xs)
            return k
        | Just (Alg (Pop k)) <- prj @(Pop s) op = eval oalg $ do
            xs <- get
            case xs of
                [] -> return (k Nothing)
                y : ys -> do
                    put ys
                    return (k (Just y))

withState :: forall s . Handler '[With s] '[Put [s], Get [s]] '[] '[]
withState = interpretM f where
    f :: Monad m => Algebra [Put [s], Get [s]] m -> Algebra '[With s] m
    f oalg op
        | Just (Scp (With f k)) <- prj @(With s) op = do
            s <- eval oalg $ do
                s <- get
                put @[s] []
                return s
            x <- k
            eval oalg $ do
                xs <- get
                put (f xs : s)
            return x
            
stack :: [s] -> Handler '[Push s, Pop s] '[] '[S.StateT [s]] '[(,) [s]]
stack xs = pushPopState ||> state xs

stackW :: [s] -> Handler '[Push s, Pop s, With s] '[] '[S.StateT [s]] '[(,) [s]]
stackW xs = (pushPopState |> withState) ||> state xs
