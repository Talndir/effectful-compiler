{-# LANGUAGE DataKinds #-}
module Typing.Typer3 where

import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E
import Control.Monad
import qualified Data.Map as M

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


type TyperEffs v f t
    = '[Fresh t, Lookup v (f t), Contains t, Modify (f t), Unify f t]

type TyperAlg effs v f t
    = CAlgebra (MakeTerm effs v) (TyperEffs v f t) (t -> f t, f t)

freshVar :: Member (Fresh t) sig => Prog sig (Ty t)
freshVar = Free <$> fresh

typerVar :: forall a v . Eq a => TyperAlg '[Var] v (Ty' a) a
typerVar (Eff (Scp (Var v))) = Const $ do
    t <- lookup v
    return (pure, t)

typerApp :: forall a v . Eq a => TyperAlg '[App] v (Ty' a) a
typerApp (Eff (Scp (App (Const m) (Const n)))) = Const $ do
    (s1, b) <- m
    (s2, a) <- modify (>>= s1) n
    t <- freshVar
    s3 <- unify (b >>= s2) (Arr a t)
    return (s1 >=> s2 >=> s3, t >>= s3)

typerAbs :: forall a v . Eq a => TyperAlg '[Abs] v (Ty' a) a
typerAbs (Eff (Scp (Abs v (Const m)))) = Const $ do
    t1 <- lookup v
    (s, t2) <- m
    return (s, Arr (t1 >>= s) t2)

typerLet :: forall a v . Eq a => TyperAlg '[Let] v (Ty' a) a
typerLet (Eff (Scp (Let x (Const m) (Const n)))) = Const $ do
    (s1, a) <- m
    t <- lookup x
    s2 <- unify t a
    (s3, b) <- modify (>>= (s1 >=> s2)) n
    return (s1 >=> s2 >=> s3, b)

typerAll :: Eq a => TyperAlg VAAL v (Ty' a) a
typerAll = typerVar ## typerApp ## typerAbs ## typerLet

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

typerH  :: forall v t f . (Ord v, Eq t, Foldable f)
        => t -> (t -> t)
        -> (f t -> f t -> Prog '[Throw String] (t -> f t))
        -> (M.Map v (f t))
        -> Handler (TyperEffs v f t) '[]
                   '[S.StateT t, S.StateT (M.Map v (f t)), E.ExceptT String] '[(,) t, (,) (M.Map v (f t)), Either String]
typerH fresh0 freshInc u m
    =  (freshState freshInc ||> state fresh0)
    |> ((contextMap |> unifyThrow u) ||> (state m |> throwT))

typeIt :: Int -> Term VAAL Int -> Term VAAL (Int, Ty Int)
typeIt w p = mapVAAL (\x -> (x, s x)) p where
    h = typerH w (+1) uni (M.fromList (map (\x -> (x, Free x)) [0..w-1]))
    Right (m, (n, (s, t))) = handle h . cfold typerAll (return, return 0) $ p

typeIt' :: Int -> Term VAAL Int -> Either String (String, Ty Int, [(Int, Ty Int)], Int)
typeIt' w p = do
    let h = typerH w (+1) uni (M.fromList (map (\x -> (x, Free x)) [0..w-1]))
    (m, (n, (s, t))) <- handle h . cfold typerAll (return, return 0) $ p
    return (showVAAL . mapVAAL (\x -> (x, s x)) $ p, t, M.toList m, n)

