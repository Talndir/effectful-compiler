{-# LANGUAGE DataKinds #-}
module Typing.Typer2 where
{-
import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E
import Control.Monad

import Control.Effect
import Control.Family.Scoped
import Control.Effect.State
import Control.Effect.Except

import Stuff
import Language.Lambda2
import Effect.Modify
import Effect.Fresh
import Effect.Unify
import Effect.Lookup

type TyperEffs v a = '[Fresh a, Lookup v (Ty a), Modify (v -> Ty a), Unify (Ty' a) a]

type TyperAlg effs v a
    = CAlgebra (MakeTerm effs v) (TyperEffs v a) (a -> Ty a, Ty a)

typerVar :: forall a v . Eq a => TyperAlg '[Var] v a
typerVar (Eff (Scp (Var v))) = Const $ do
    t <- lookup v
    return (pure, t)

typerApp :: forall a v . Eq a => TyperAlg '[App] v a
typerApp (Eff (Scp (App (Const m) (Const n)))) = Const $ do
    (s3, b) <- m
    (s2, a) <- modify @(v -> Ty a) (>=> s3) n
    t <- Free <$> fresh
    s1 <- unify @(Ty' a) @a (b >>= s2) (Arr a t)
    return (s3 >=> s2 >=> s1, t >>= s1)

typerAbs :: forall a v . Eq a => TyperAlg '[Abs] v a
typerAbs (Eff (Scp (Abs v (Const m)))) = Const $ do
    t1 <- lookup v
    (s, t2) <- m
    return (s, Arr (t1 >>= s) t2)

typerAll :: Eq a => TyperAlg VAA v a
typerAll = typerVar ## typerApp ## typerAbs

err :: Prog '[Throw String] a
err = throw "Unification failure"

uni :: Eq a => Ty a -> Ty a -> Prog '[Throw String] (a -> Ty a)
uni (Free x) t = case x `elem` t of
    True -> err
    False -> return (aug x t pure)
uni t (Free x) = uni (Free x) t
uni (Arr t1 t2) (Arr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (t2 >>= s1) (w2 >>= s1)
    return (s1 >=> s2)
uni (Bound x) (Bound y)
    | x == y = return pure
    | otherwise = err
uni (Fixed x) (Fixed y)
    | x == y = return pure
    | otherwise = err
uni _ _ = err

typerH  :: t -> (t -> t)
        -> (f t -> f t -> Prog '[Throw e] (t -> f t)) -> (v -> f t)
        -> Handler '[Fresh t, Lookup v (f t), Modify (v -> f t), Unify f t] '[]
                   '[S.StateT t, S.StateT (v -> f t), E.ExceptT e] '[(,) t, (,) (v -> f t), Either e]
typerH fresh0 freshInc u look0
    =  (freshState freshInc ||> state fresh0)
    |> (contextState ||> state look0)
    |> (unifyThrow u ||> throwT)

typeIt :: Term VAA (Int, Ty Int) -> Term VAA (Int, Ty Int)
typeIt t = mapVAA (fmap (>>= s)) t where
    h = typerH 10 (+1) uni snd
    Right (_, (_, (s, _))) = handle h . cfold typerAll (return, return 0) $ t
-}
