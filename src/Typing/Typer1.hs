{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Typing.Typer1 where

import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.State
import Control.Effect.Except

import Language.Lambda1
import Effect.Modify
import Effect.Fresh


instance Member (Throw String) sig => MonadFail (Prog sig) where
    fail = throw

type Unify t = Alg (Unify' t)
data Unify' t a where
    Unify :: t -> t -> ((t -> t) -> a) -> Unify' t a
    deriving Functor

unify :: Member (Unify t) sig => t -> t -> Prog sig (t -> t)
unify x y = call (Alg (Unify x y return))

type Lookup v t = Alg (Lookup' v t)
data Lookup' v t a where
    Lookup :: v -> (t -> a) -> Lookup' v t a
    deriving Functor

lookup :: Member (Lookup v t) sig => v -> Prog sig t
lookup v = call (Alg (Lookup v return))



typingState :: forall t v e . (t -> t -> Prog '[Throw e] (t -> t))
            -> Handler '[Unify t, Lookup v t, Modify (v -> t)] '[Put (v -> t), Get (v -> t), Throw e] '[] '[]
typingState u = interpretM f where
    f :: Monad m => (forall x. Effs '[Put (v -> t), Get (v -> t), Throw e] m x -> m x)
        -> forall x. Effs '[Unify t, Lookup v t, Modify (v -> t)] m x -> m x
    f oalg op
        | Just (Alg (Unify t1 t2 k)) <- prj @(Unify t) op = eval oalg . weakenProg $ do
            t <- u t1 t2
            return (k t)
        | Just (Alg (Lookup v k)) <- prj @(Lookup v t)op = eval oalg $ do
            w <- get
            return (k (w v))
        | Just (Scp (Modify g k)) <- prj @(Modify (v -> t))op = do
            w <- eval oalg $ do
                w <- get @(v -> t)
                put (g w)
                return w
            x <- k
            eval oalg (put w)
            return x
        | otherwise = undefined

q :: forall t v e . (t -> t -> Prog '[Throw e] (t -> t))
            -> Handler '[Unify t, Lookup v t, Modify (v -> t), Throw e] '[Put (v -> t), Get (v -> t), Throw e] '[] '[]
q u = relax' @'[Unify t, Lookup v t, Modify (v -> t)] @'[Throw e] (typingState u)


throwAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs '[Throw e] (E.ExceptT e m) x -> E.ExceptT e m x)
throwAlg _ (Eff (Alg (Throw e))) = E.ExceptT (return (Left e))

throwT :: Handler '[Throw e] '[] '[E.ExceptT e] '[Either e]
throwT = handler E.runExceptT throwAlg

typer2  :: forall v t e . t -> (t -> t)
        -> (t -> t -> Prog '[Throw e] (t -> t)) -> (v -> t)
        -> Handler '[Fresh t, Unify t, Lookup v t, Modify (v -> t)] '[]
                   '[S.StateT t, S.StateT (v -> t), E.ExceptT e] '[(,) t, (,) (v -> t), Either e]
typer2 fresh0 freshInc u look0
    =  (freshState freshInc ||> state fresh0)
    |> (typingState u ||> (state look0 |> throwT))


extend :: Eq v => v -> t -> (v -> t) -> (v -> t)
extend v t f x
    | x == v = t
    | otherwise = f x

apply :: (t -> t) -> (v -> t) -> (v -> t)
apply = (.)

typer :: forall v a . Eq a => Term v -> Prog '[Fresh (Ty a), Unify (Ty a), Lookup v (Ty a), Modify (v -> Ty a)] (Ty a -> Ty a, Ty a)
typer (Var v) = do
    t <- lookup v
    return (id, t)
typer (App m n) = do
    (s3, b) <- typer m
    (s2, a) <- modify @(v -> Ty a) (s3 .) (typer n)
    t <- fresh
    s1 <- unify @(Ty a) (s2 b) (TArr a t)
    return (s1 . s2 . s3, s1 t)
typer (Lam x m) = do
    t1 <- lookup x
    (s, t2) <- typer m
    return (s, TArr (s t1) t2)

uni :: Eq a => Ty a -> Ty a -> Prog '[Throw String] (Ty a -> Ty a)
uni (TVar x) (TVar y) = return (extend (TVar x) (TVar y) id)
uni (TVar x) t = case x `elem` t of
    True -> fail "Unification failure"
    False -> return (extend (TVar x) t id)
uni t (TVar x) = uni (TVar x) t
uni (TArr t1 t2) (TArr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (s1 t2) (s1 w2)
    return (s2 . s1)


typeIt :: Term (Int, Ty Int) -> Term (Int, Ty Int)
typeIt t = fmap (fmap s) t where
    h = typer2 (TVar 10) (fmap (+1)) uni snd
    Right (_, (_, (s, _))) = handle h (typer t)
