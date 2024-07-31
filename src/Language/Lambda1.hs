{-# LANGUAGE DataKinds #-}
module Language.Lambda1 where

import Prelude hiding (lookup)

import Control.Effect
import Control.Effect.State

import Effect.Map
import Effect.Fresh

data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam a (Term a)
    deriving Functor

instance Show a => Show (Term a) where
    showsPrec p e = case e of
        Var x -> shows x
        App t1 t2 ->
            showParen (p > appPrec)
            ( showsPrec appPrec t1
            . showString " "
            . showsPrec (appPrec + 1) t2)
        Lam x t ->
            showParen (p > lamPrec)
            ( showString "λ "
            . shows x
            . showString " . "
            . showsPrec (lamPrec + 1) t)
        where
            appPrec = 10
            lamPrec = 5

data Ty a
    = TVar a
    | TArr (Ty a) (Ty a)
    deriving (Eq, Foldable, Functor, Traversable)


instance Show a => Show (Ty a) where
    showsPrec p t = case t of
        TVar x -> shows x
        TArr t1 t2 ->
            showParen (p > arrPrec)
            ( showsPrec arrPrec t1
            . showString " -> "
            . showsPrec (arrPrec + 1) t2)
        where
            arrPrec = 10

type Renamer a = '[Fresh Int, Map a (Int, Ty Int)]

new :: Eq a => Prog (Renamer a) (Int, Ty Int)
new = do
    n <- fresh @Int
    return (n, TVar n)

rename :: (Eq a, Ord a) => Term a -> Term (Int, Ty Int)
rename = snd . snd . handle h . rename' where

    h = (freshState (+1) ||> state (0 :: Int)) |> mapH

    rename' :: Eq a => Term a -> Prog (Renamer a) (Term (Int, Ty Int))
    rename' (Var x) = do
        t <- lookup x
        case t of
            Just t' -> return (Var t')
            Nothing -> do
                w <- new
                insert x w
                return (Var w)
    rename' (App m n) = do
        m' <- rename' m
        n' <- rename' n
        return (App m' n')
    rename' (Lam x m) = do
        w <- new
        m' <- extend x w (rename' m)
        return (Lam w m')
