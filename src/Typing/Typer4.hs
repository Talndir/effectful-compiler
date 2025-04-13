{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Typing.Typer4 where

import Prelude hiding (lookup)
import Data.List (intersperse)
import qualified Control.Monad.Trans.State.Strict as S
import Control.Monad.Trans.Except as E
import qualified Data.Map as M

import Control.Effect
import Control.Family.Algebraic
import Control.Family.Scoped
import Control.Effect.State
import Control.Effect.Except

import Stuff
import Language.Lambda2
import Effect.Modify
import Effect.Fresh
import Effect.Unify
import Effect.Lookup
import Effect.Stack
import Effect.Label

{-

Effects:
    freshVar :: Get a fresh type
        - Fresh (f t)
        - Handle with regular Fresh handler with f = fmap (+1)
    getType v :: Get the stored type of a variable
        - GetType v (f t)
        - Literally just a function v -> f t
        - Store the type inside v and extract
    unify t1 t2 :: Unify two types
        - Unify f t
        - Standard implementation
        - Handles to Throw
    lookup v :: Look up the type of v in the context
        - Lookup v (f t)
        - Looks up the name associated with v, then applies the stored substitution
        - Handle to State (Map v (f t), Subst) (uses both map and subst)
    modify s k :: Run subprogram with an updated stored substitution
        - Modify (f t)
        - Handle to State (Map v (f t), Subst) (uses only subst)
    extend v t k :: Run subprogram with extended variable context
        - Extend v (f t)
        - Handle to State (Map v (f t), Subst) (uses only map)
    with m k :: Run subprogram in the context m
        - Label (Term (_ v))
        - Handle to Stack (Term (_ v))

Preprocessing:
    v ~ (String, Int, Ty Int)
        - String = Original name
        - Int = New name, unique
        - Ty Int = New type, unique/given (not unified)
    f ~ Ty
    t ~ Int

    Make all names and types unique, but don't unify user-given types with generated types
    Wrap all operations with a Label (Term (_ String)) that holds the original term, with
    the original names and the user-given types

Algebra:
    Var v: Look up v, get type of v, unify
    App m n: As usual
    Abs x m: Get type of x, extend m with x, rest as usual
    Let x m n: Type m, get type of x, unify, extend n with x, rest as usual
    Label p k: Run k with p

-}

type GetType v t = Alg (GetType' v t)
data GetType' v t a where
    GetType :: v -> (t -> a) -> GetType' v t a
    deriving Functor

getType :: Member (GetType v t) sig => v -> Prog sig t
getType x = call (Alg (GetType x return))

type TyperEffs v f t
    = '[  Fresh (f t)
        , Lookup v (f t)
        , Modify (t -> f t)
        , Extend v (f t)
        , Unify f t
        , GetType v (f t)
        , Push (Int, Int)
        , Pop (Int, Int)
        ]

type TyperAlg effs v f t
    = PAlg effs (TyperEffs v f t) (t -> f t, f t)

typerVar :: forall a v. Eq a => TyperAlg '[Var v] v Ty a
typerVar (CVar (x :: v)) = do
    t <- lookup x
    t' <- getType x
    s <- unify t t'
    return (s, s #$ t)

typerApp :: Eq a => TyperAlg '[App] v Ty a
typerApp (CApp m n) = do
    (s1, b) <- m
    (s2, a) <- modify (#> s1) n
    t <- fresh
    s3 <- unify (s2 #$ b) (Arr a t)
    return (s1 #> s2 #> s3, s3 #$ t)

typerAbs :: forall a v . Eq a => TyperAlg '[Abs v] v Ty a
typerAbs (CAbs (x :: v) m) = do
    t1 <- getType x
    (s, t2) <- extend x t1 m
    return (s, Arr (s #$ t1) t2)

typerLet :: forall a v . Eq a => TyperAlg '[Let v] v Ty a
typerLet (CLet (x :: v) m n) = do
    (s1, a) <- m
    t <- getType x
    s2 <- unify t a
    (s3, b) <- extend x (s2 #$ t) $ modify (#> (s1 #> s2)) n
    return (s1 #> s2 #> s3, b)

typerLabel :: forall a v . TyperAlg '[Label Pos] v Ty a
typerLabel (Eff (Scp (Label x (Const p)))) = extra x p

typerVAAL :: forall a v . Eq a => TyperAlg (VAAL v) v Ty a
typerVAAL = typerVar ## typerApp @_ @v ## typerAbs ## typerLet

typerLVAAL :: forall a v . Eq a => TyperAlg (Label Pos ': VAAL v) v Ty a
typerLVAAL = typerLabel @a @v ## typerVar ## typerApp @_ @v ## typerAbs ## typerLet

err :: Show b => b -> b -> String -> Prog '[Throw String] a
err t1 t2 s = throw $ "Type inference failed: could not unify " ++ show t1 ++ " and " ++ show t2 ++ w where
    w = case s of
        "" -> ""
        _ -> "\n\t" ++ s

uni :: (Eq a, Show a) => Ty a -> Ty a -> Prog '[Throw String] (a -> Ty a)
uni (Free x) (Free y) = case x == y of
    True -> return Free
    False -> return (aug x (Free y) Free)
uni (Free x) t = case x `elem` t of
    True -> err (Free x) (t) $ show (Free x) ++ " occurs in " ++ show t
    False -> return (aug x t Free)
uni t (Free x) = uni (Free x) t
uni (Arr t1 t2) (Arr w1 w2) = do
    s1 <- uni t1 w1
    s2 <- uni (s1 #$ t2) (s1 #$ w2)
    return (s1 #> s2)
uni (Bound x) (Bound y)
    | x == y = return Free
    | otherwise = err (Bound x) (Bound y) $ "The type variables are distinct and cannot be unified"
uni t1@(Fixed x) t2@(Fixed y)
    | x == y = return Free
    | otherwise = err t1 t2 $ "The types are different and cannot be unified"
uni t1 t2 = err t1 t2 ""


type V = (String, Int, Ty Int)
type F = Ty
type T = Int
type M = M.Map Int (String, Ty Int)
type S = Int -> Ty Int

getTypeH :: (a -> b) -> Handler '[GetType a b] '[] '[] '[]
getTypeH f = interpret $ \(Eff (Alg (GetType x k))) -> return (k (f x))

conMap :: Handler  '[Lookup V (F T), Modify (T -> F T), Extend V (F T)]
                   '[Put (M, S), Get (M, S), Throw String]
                   '[] '[]
conMap = interpretM f where
    f :: Monad m
        => Algebra '[Put (M, S), Get (M, S), Throw String] m
        -> Algebra '[Lookup V (F T), Modify (T -> F T), Extend V (F T)] m
    f oalg op
        | Just (Alg (Lookup (n, w, _) k)) <- prj @(Lookup V (F T)) op = eval oalg $ do
            (m, s) <- get @(M, S)
            case M.lookup w m of
                Nothing -> do
                    throw $ "Error: Coud not find variable " ++ n ++ " in context"
                Just (_, t) -> return (k (s #$ t))
        | Just (Scp (Modify g k)) <- prj @(Modify (T -> F T)) op = do
            w <- eval oalg $ do
                (m, s) <- get @(M, S)
                put (m, g s)
                return (m, s)
            x <- k
            eval oalg (put w)
            return x
        | Just (Scp (Extend (n, v, _) t k)) <- prj @(Extend V (F T)) op = do
            w <- eval oalg $ do
                (m, s) <- get @(M, S)
                put (M.insert v (n, t) m, s)
                return (m, s)
            x <- k
            eval oalg $ put w
            return x
        | otherwise = undefined

reThrow :: String -> Handler '[Throw String] '[Put (M, S), Get (M, S), Throw String, Put [Pos], Get [Pos]] '[] '[]
reThrow q = interpret $ \(Eff (Alg (Throw e))) -> do
    (m, s) <- get @(M, S)
    ps <- get @[Pos]
    throw (printErr e s m ps)
    where
        printVar s (n, t) = "\t" ++ n ++ " :: " ++ show (s #$ t)
        printCon s m = concat . intersperse "\n" . map (printVar s) . M.elems $ m
        printTerm (a, b) = "in the expression " ++ take b (drop a q)
        printTerms = concat . intersperse "\n" . map printTerm
        printErr e s m ps = e
            ++ "\nCurrent context:\n" ++ printCon s m
            ++ "\n" ++ printTerms ps

typerH1 :: Int -> Handler
             (TyperEffs V F T)
            '[Put (M, S), Get (M, S), Throw String, Put [Pos], Get [Pos]]
            '[S.StateT (Ty Int)]
            '[(,) (Ty Int)]
typerH1 s =     (freshState (\(Free x) -> Free (x + 1)) ||> state (Free s))
            |>  conMap
            |>  unifyThrow uni
            |>  getTypeH (\(_, _, t) -> t)
            |>  pushPopState

typerH2 :: String -> Handler
            '[Put (M, S), Get (M, S), Throw String, Put [Pos], Get [Pos]]
            '[]
            '[S.StateT (M, S), S.StateT [Pos], E.ExceptT String]
            '[(,) (M, S), (,) [Pos], Either String]
typerH2 q = relaxL @[Put (M, S), Get (M, S)] (relaxR @[Put [Pos], Get [Pos]] $ reThrow q)
      ||> (state (M.empty, Free) |> state [] |> throwT)

typer :: String -> Int -> Term (Label Pos ': VAAL (String, Int)) -> Either String (Term (Label Pos ': VAAL (String, Ty Int)))
typer k w p = do
    let q = mapLVAAL (\(n, t) -> (n, t, Free t)) p
    let r = cfold (return (Free, Free 0)) typerLVAAL q
    (_, (_, (_, (s, t)))) <- handle (typerH1 w ||> typerH2 k) r
    return (mapLVAAL (\(n, v) -> (n, s v)) p)
