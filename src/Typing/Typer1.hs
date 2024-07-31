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
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.State
import Control.Effect.Except

import Language.Lambda1
import Effect.Modify
import Effect.Fresh


instance Member (Throw String) sig => MonadFail (Prog sig) where
    fail = throw

type Unify f t = Alg (Unify' f t)
data Unify' f t a where
    Unify :: Eq t => f t -> f t -> ((t -> f t) -> a) -> Unify' f t a

instance Functor (Unify' f t) where
    fmap f (Unify t1 t2 k) = Unify t1 t2 (f . k)

unify :: (Member (Unify f t) sig, Eq t) => f t -> f t -> Prog sig (t -> f t)
unify x y = call (Alg (Unify x y return))

type Lookup v t = Alg (Lookup' v t)
data Lookup' v t a where
    Lookup :: v -> (t -> a) -> Lookup' v t a
    deriving Functor

lookup :: Member (Lookup v t) sig => v -> Prog sig t
lookup v = call (Alg (Lookup v return))



typingState :: forall t v e f . (f t -> f t -> Prog '[Throw e] (t -> f t))
            -> Handler '[Unify f t, Lookup v (f t), Modify (v -> f t)] '[Put (v -> f t), Get (v -> f t), Throw e] '[] '[]
typingState u = interpretM f where
    f :: Monad m => (forall x. Effs '[Put (v -> f t), Get (v -> f t), Throw e] m x -> m x)
        -> forall x. Effs '[Unify f t, Lookup v (f t), Modify (v -> f t)] m x -> m x
    f oalg op
        | Just (Alg (Unify t1 t2 k)) <- prj @(Unify f t) op = eval oalg . weakenProg $ do
            t <- u t1 t2
            return (k t)
        | Just (Alg (Lookup v k)) <- prj @(Lookup v (f t))op = eval oalg $ do
            w <- get
            return (k (w v))
        | Just (Scp (Modify g k)) <- prj @(Modify (v -> f t))op = do
            w <- eval oalg $ do
                w <- get @(v -> f t)
                put (g w)
                return w
            x <- k
            eval oalg (put w)
            return x
        | otherwise = undefined

throwAlg :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x. Effs '[Throw e] (E.ExceptT e m) x -> E.ExceptT e m x)
throwAlg _ (Eff (Alg (Throw e))) = E.ExceptT (return (Left e))

throwT :: Handler '[Throw e] '[] '[E.ExceptT e] '[Either e]
throwT = handler E.runExceptT throwAlg

typer2  :: t -> (t -> t)
        -> (f t -> f t -> Prog '[Throw e] (t -> f t)) -> (v -> f t)
        -> Handler '[Fresh t, Unify f t, Lookup v (f t), Modify (v -> f t)] '[]
                   '[S.StateT t, S.StateT (v -> f t), E.ExceptT e] '[(,) t, (,) (v -> f t), Either e]
typer2 fresh0 freshInc u look0
    =  (freshState freshInc ||> state fresh0)
    |> (typingState u ||> (state look0 |> throwT))


extend :: Eq v => v -> t -> (v -> t) -> (v -> t)
extend v t f x
    | x == v = t
    | otherwise = f x

apply :: (t -> t) -> (v -> t) -> (v -> t)
apply = (.)

typer :: forall v a . Eq a => Term v -> Prog '[Fresh a, Unify Ty a, Lookup v (Ty a), Modify (v -> Ty a)] (a -> Ty a, Ty a)
typer (Var v) = do
    t <- lookup v
    return (pure, t)
typer (App m n) = do
    (s3, b) <- typer m
    (s2, a) <- modify @(v -> Ty a) (>=> s3) (typer n)
    t <- TVar <$> fresh
    s1 <- unify @Ty @a (b >>= s2) (TArr a t)
    return (s3 >=> s2 >=> s1, t >>= s1)
typer (Lam x m) = do
    t1 <- lookup x
    (s, t2) <- typer m
    return (s, TArr (t1 >>= s) t2)

uni :: Eq a => Ty a -> Ty a -> Prog '[Throw String] (a -> Ty a)
uni (TVar x) (TVar y) = return (extend x (TVar y) pure)
uni (TVar x) t = case x `elem` t of
    True -> fail "Unification failure"
    False -> return (extend x t pure)
uni t (TVar x) = uni (TVar x) t
uni (TArr t1 t2) (TArr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (t2 >>= s1) (w2 >>= s1)
    return (s1 >=> s2)


typeIt :: Term (Int, Ty Int) -> Term (Int, Ty Int)
typeIt t = fmap (fmap (>>= s)) t where
    h = typer2 10 (+1) uni snd
    Right (_, (_, (s, _))) = handle h (typer t)
