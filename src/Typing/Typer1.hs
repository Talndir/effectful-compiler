{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Typing.Typer1 where

import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E
import Control.Monad

import Control.Effect
import Control.Effect.State
import Control.Effect.Except

import Stuff
import Language.Lambda1
import Effect.Modify
import Effect.Fresh
import Effect.Unify
import Effect.Lookup

typerH  :: Monad f
        => t -> (t -> t)
        -> (f t -> f t -> Prog '[Throw e] (t -> f t)) -> (t -> f t)
        -> Handler '[Fresh t, Lookup t (f t), Modify (t -> f t), Unify f t] '[]
                   '[S.StateT t, S.StateT (t -> f t), E.ExceptT e] '[(,) t, (,) (t -> f t), Either e]
typerH fresh0 freshInc u look0
    =  (freshState freshInc ||> state fresh0)
    |> (contextState ||> state look0)
    |> (unifyThrow u ||> throwT)

freshVar :: Member (Fresh t) sig => Prog sig (Ty t)
freshVar = TVar <$> fresh

typer :: forall v t . (Eq v, Eq t) => Term v
    -> Prog '[Fresh t, Lookup v (Ty t), Modify (v -> Ty t), Unify Ty t] (t -> Ty t, Ty t)
typer (Var v) = do
    t <- lookup v
    return (pure, t)
typer (App m n) = do
    (s1, b) <- typer m
    (s2, a) <- modify @(v -> Ty t) (>=> s1) (typer n)
    t <- TVar <$> fresh
    s3 <- unify @Ty (b >>= s2) (TArr a t)
    return (s1 >=> s2 >=> s3, t >>= s3)
typer (Lam x m) = do
    t1 <- freshVar
    (s, t2) <- modify (aug x t1) (typer m)
    return (s, TArr (t1 >>= s) t2)

uni :: Eq a => Ty a -> Ty a -> Prog '[Throw String] (a -> Ty a)
uni (TVar x) (TVar y) = return (aug x (TVar y) pure)
uni (TVar x) t = case x `elem` t of
    True -> throw $ "Unification failure"
    False -> return (aug x t pure)
uni t (TVar x) = uni (TVar x) t
uni (TArr t1 t2) (TArr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (t2 >>= s1) (w2 >>= s1)
    return (s1 >=> s2)


typeIt :: Term Int -> Either String (Term (Int, Ty Int))
typeIt t = do
    let h = typerH 0 (+1) uni return
    (_, (_, (s, _))) <- handle h (typer t)
    return (fmap (\x -> (x, s x)) t)
