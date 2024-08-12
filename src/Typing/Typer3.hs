{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Typing.Typer3 where

import Prelude hiding (lookup)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E
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
    = PAlg effs (TyperEffs v f t) (t -> f t, f t)

freshVar :: Member (Fresh t) sig => Prog sig (Ty t)
freshVar = Free <$> fresh

typerVar :: Eq a => TyperAlg '[Var v] v Ty a
typerVar (Eff (Scp (Var v))) = do
    t <- lookup v
    return (Free, t)

typerApp :: Eq a => TyperAlg '[App] v Ty a
typerApp (Eff (Scp (App (Const m) (Const n)))) = do
    (s1, b) <- m
    (s2, a) <- modify (s1 #$) n
    t <- freshVar
    s3 <- unify (s2 #$ b) (Arr a t)
    return (s1 #> s2 #> s3, s3 #$ t)

typerAbs :: Eq a => TyperAlg '[Abs v] v Ty a
typerAbs (Eff (Scp (Abs v (Const m)))) = do
    t1 <- lookup v
    (s, t2) <- m
    return (s, Arr (s #$ t1) t2)

typerLet :: Eq a => TyperAlg '[Let v] v Ty a
typerLet (Eff (Scp (Let x (Const m) (Const n)))) = do
    (s1, a) <- m
    t <- lookup x
    s2 <- unify t a
    (s3, b) <- modify ((s1 #> s2) #$) n
    return (s1 #> s2 #> s3, b)

typerVAAL :: forall a v . Eq a => TyperAlg (VAAL v) v Ty a
typerVAAL = typerVar ## typerApp @_ @v ## typerAbs ## typerLet

err :: Prog '[Throw String] a
err = throw "Unification failure"

uni :: Eq a => Ty a -> Ty a -> Prog '[Throw String] (a -> Ty a)
uni (Free x) t = case x `elem` t of
    True -> err
    False -> return (aug x t Free)
uni t (Free x) = uni (Free x) t
uni (Arr t1 t2) (Arr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (s1 #$ t2) (s1 #$ w2)
    return (s1 #> s2)
uni (Bound x) (Bound y)
    | x == y = return Free
    | otherwise = err
uni (Fixed x) (Fixed y)
    | x == y = return Free
    | otherwise = err
uni _ _ = err

typerH  :: forall v t f . (Ord v, Eq t, Foldable f)
        => t -> (t -> t)
        -> (forall w . Eq w => f w -> f w -> Prog '[Throw String] (w -> f w))
        -> (M.Map v (f t))
        -> Handler (TyperEffs v f t) '[]
                   '[S.StateT t, S.StateT (M.Map v (f t)), E.ExceptT String] '[(,) t, (,) (M.Map v (f t)), Either String]
typerH fresh0 freshInc u m
    =  (freshState freshInc ||> state fresh0)
    |> ((contextMap |> unifyThrow u) ||> (state m |> throwT))

typeIt' :: Int -> Term (VAAL Int) -> Either String (String, Ty Int, [(Int, Ty Int)], Int)
typeIt' w p = do
    let h = typerH w (+1) uni (M.fromList (map (\x -> (x, Free x)) [0..w-1]))
    (m, (n, (s, t))) <- handle h . cfold (return (Free, Free 0)) typerVAAL $ p
    return (showVAAL . mapVAAL (\x -> (x, s x)) $ p, t, M.toList m, n)

