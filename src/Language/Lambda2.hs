{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Lambda2 where

import Prelude hiding (lookup, abs)

import Control.Monad
import qualified Control.Monad.Trans.State.Strict as S
import Data.List (intersperse)
import qualified Data.Map as M

import Control.Effect
import Control.Family.Scoped
import Control.Effect.State

import Stuff
import Effect.Map
import Effect.Fresh
import Effect.Label

type Var a = Scp (Var' a)
data Var' a k where
    Var :: a -> Var' a k
    deriving Functor

var :: forall a b sig . Member (Var a) sig => a -> Prog sig b
var x = call @(Var a) (Scp (Var x))

pattern Var' :: forall a sig b . Member (Var a) sig => a -> Prog sig b
pattern Var' x <- (Call (prj @(Var a) -> Just (Scp (Var x))) _ _)

type Abs a = Scp (Abs' a)
data Abs' a k where
    Abs :: a -> k -> Abs' a k
    deriving Functor

abs :: forall a b sig . Member (Abs a) sig => a -> Prog sig b -> Prog sig b
abs x m = call @(Abs a) (Scp (Abs x (fmap return m)))

pattern Abs' :: forall a sig b . Member (Abs a) sig => a -> Prog sig b -> Prog sig b
pattern Abs' x p <- (prj2 @(Abs a) -> Just (Scp (Abs x (join -> p))))

type App = Scp App'
data App' k where
    App :: k -> k -> App' k
    deriving Functor

app :: forall b sig . Member App sig => Prog sig b -> Prog sig b -> Prog sig b
app m n = call @App (Scp (App (fmap return m) (fmap return n)))

pattern App' :: forall sig b . Member App sig => Prog sig b -> Prog sig b -> Prog sig b
pattern App' m n <- (prj2 @App -> Just (Scp (App (join -> m) (join -> n))))

pattern CApp :: forall sig a b . Member App sig => a -> a -> Effs sig (Const a) b
pattern CApp m n <- (prj @App -> Just (Scp (App (unConst -> m) (unConst -> n))))

--pattern App' :: forall sig b . Member App sig => Prog sig b -> Prog sig b -> Prog sig b

type Let a = Scp (Let' a)
data Let' a k where
    Let :: a -> k -> k -> Let' a k
    deriving Functor

lett :: forall a b sig . Member (Let a) sig => a -> Prog sig b -> Prog sig b -> Prog sig b
lett x p q = call @(Let a) (Scp (Let x (fmap return p) (fmap return q)))

pattern Let' :: forall a sig b . Member (Let a) sig => a -> Prog sig b -> Prog sig b -> Prog sig b
pattern Let' x m n <- (prj2 @(Let a) -> Just (Scp (Let x (join -> m) (join -> n))))


data FixedType = FInt | FBool
    deriving Eq

instance Show FixedType where
    show FInt = "Int"
    show FBool = "Bool"

data Ty' c a
    = TFree a
    | TBound c
    | TFixed FixedType
    | TArr (Ty' c a) (Ty' c a)
    | TForall c (Ty' c a)
    deriving (Eq, Functor, Foldable)

newtype Ty a = Ty { unTy :: Ty' a a }
    deriving Eq

instance Show a => Show (Ty a) where
    show (Ty x) = show x

(#$) :: (a -> Ty a) -> Ty a -> Ty a
(#$) f (Ty x) = Ty (x >>= unTy . f)

(#>) :: (a -> Ty a) -> (a -> Ty a) -> (a -> Ty a)
(#>) f g x = g #$ f x

instance Foldable Ty where
    foldr f a (Ty x) = foldr f a x

pattern Free :: a -> Ty a
pattern Free x = Ty (TFree x)

pattern Bound :: a -> Ty a
pattern Bound x = Ty (TBound x)

pattern Fixed :: FixedType -> Ty a
pattern Fixed t = Ty (TFixed t)

pattern Arr :: Ty a -> Ty a -> Ty a
pattern Arr x y <- Ty (TArr (Ty -> x) (Ty -> y)) where
    Arr (Ty x) (Ty y) = Ty (TArr x y)

pattern Forall :: a -> Ty a -> Ty a
pattern Forall x t <- Ty (TForall x (Ty -> t)) where
    Forall x (Ty t) = Ty (TForall x t)

instance Applicative (Ty' c) where
    pure = TFree
    (<*>) = ap

instance Monad (Ty' c) where
    TFree x >>= f = f x
    TBound x >>= _ = TBound x
    TFixed x >>= _ = TFixed x
    TArr t1 t2 >>= f = TArr (t1 >>= f) (t2 >>= f)
    TForall x t >>= f = TForall x (t >>= f)

instance (Show c, Show a) => Show (Ty' c a) where
    showsPrec p k = case k of
        TFree x -> showString "'" . shows x
        TBound x -> shows x
        TFixed x -> shows x
        TArr t1 t2 ->
            showParen (p > arrPrec)
            ( showsPrec (arrPrec + 1) t1
            . showString " -> "
            . showsPrec arrPrec t2)
        TForall x t -> showForall [x] t
        where
            arrPrec = 10

            showForall :: [c] -> Ty' c a -> ShowS
            showForall xs (TForall x t) = showForall (x:xs) t
            showForall xs t = showString "∀ " . f (reverse xs) . showString " . " . shows t

            f xs = foldl (.) id . intersperse (showString " ") . map shows $ xs


type VAA a = [Var a, App, Abs a]
type VAAL a = [Var a, App, Abs a, Let a]

type Term effs = Prog effs ()


type SubstAlg a effs
    =  forall oeffs . Members effs oeffs
    => a -> Term oeffs -> CAlg effs (Term oeffs)

type Subst a effs
    = Eq a => a -> Term effs -> Term effs -> Term effs

substVar :: Eq a => SubstAlg a '[Var a]
substVar v p (Eff (Scp (Var x)))
    | x == v = p
    | otherwise = var x

substApp :: SubstAlg a '[App]
substApp _ _ (Eff (Scp (App (Const m) (Const n)))) = app m n

substAbs :: SubstAlg a '[Abs a]
substAbs _ _ (Eff (Scp (Abs x (Const m)))) = abs x m

substLet :: SubstAlg a '[Let a]
substLet _ _ (Eff (Scp (Let x (Const m) (Const n)))) = lett x m n


substVAAL :: forall a . Subst a (VAAL a)
substVAAL v p = cfold (return ()) alg where
    alg :: CAlg (VAAL a) (Term (VAAL a))
    alg = substVar v p ## substApp v p ## substAbs v p ## substLet v p


type Reduce a effs
    =  forall effs' . Members effs effs'
    => Subst a effs'
    -> (Term effs' -> Maybe (Term effs'))
    -> Term effs' -> Maybe (Term effs')

reduceVar :: forall a . Eq a => Reduce a '[Var a]
reduceVar _ _ (Var' (_ :: a)) = Nothing
reduceVar _ _ _ = Nothing

reduceAbs :: forall a . Reduce a '[Abs a]
reduceAbs _ _ (Abs' (_ :: a) _) = Nothing
reduceAbs _ _ _ = Nothing

reduceApp :: Eq a => Reduce a '[App, Abs a]
reduceApp f _ (App' (Abs' (x :: a) m) n) = Just (f x n m)
reduceApp _ g (App' m n) = case g m of
    Just m' -> Just (app m' n)
    Nothing -> case g n of
        Just n' -> Just (app m n')
        Nothing -> Nothing
reduceApp _ _ _ = Nothing

reduceLet :: Eq a => Reduce a '[Let a]
reduceLet f _ (Let' (x :: a) m n) = Just (f x m n)
reduceLet _ _ _ = Nothing

(>~>) :: (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
(>~>) f g x = case f x of
    Nothing -> g x
    Just y -> Just y

reduceVAAL :: forall a . Eq a => Term (VAAL a) -> Maybe (Term (VAAL a))
reduceVAAL = reduceVar s r >~> reduceAbs s r >~> reduceApp s r >~> reduceLet s r where
    s = substVAAL
    r = reduceVAAL

iterM :: (a -> Maybe a) -> a -> [a]
iterM f x = case f x of
    Nothing -> [x]
    Just y -> x : iterM f y

exec :: Eq a => Term (VAAL a) -> [Term (VAAL a)]
exec = iterM reduceVAAL


ff :: Injects effs effs' => a -> Effs effs (Const (Prog effs' a)) x -> Prog effs' a
ff x eff = Call (injs eff) (fmap (const undefined) . unConst) (const (return x))

optId :: forall a effs . (Eq a, Members '[Var a, Abs a, App] effs, Injects effs effs)
    => CAlg effs (Term effs)
optId (CApp (Abs' (x :: a) (Var' (y :: a))) n)
    | x == y = n
    | otherwise = var y
optId op = ff () op

opt :: forall a effs . (Eq a, Members '[Var a, Abs a, App] effs, Injects effs effs) => Term effs -> Term effs
opt op = cfold (return ()) (optId @a) op


type ShowAlg effs
    = CAlg effs (Int -> ShowS)

showVar :: Show a => ShowAlg '[Var a]
showVar (Eff (Scp (Var x))) = \_ -> shows x

showApp :: ShowAlg '[App]
showApp (Eff (Scp (App (Const m) (Const n)))) = \p -> 
    showParen (p > 10)
    ( m 10
    . showString " "
    . n 11)

showAbs :: Show a => ShowAlg '[Abs a]
showAbs (Eff (Scp (Abs x (Const m)))) = \p ->
    showParen (p > 5)
    ( showString "λ "
    . shows x
    . showString " . "
    . m 0)

showLet :: Show a => ShowAlg '[Let a]
showLet (Eff (Scp (Let x (Const m) (Const n)))) = \p ->
    showParen (p > 5)
    ( showString "let "
    . shows x
    . showString " = "
    . m 0
    . showString " in "
    . n 0)

showAnn :: Show t => ShowAlg '[Label t]
showAnn (Eff (Scp (Label t (Const m)))) = \p ->
    showParen True
    ( shows t
    . showString " :: "
    . m 0 )

showVAAL :: forall a . Show a => Term (VAAL a) -> String
showVAAL p = cfold (\_ _ -> "") alg p 0 "\n" where
    alg :: ShowAlg (VAAL a)
    alg = showVar @a ## showApp ## showAbs @a ## showLet @a


type MapAlg effs effs' a b
    = (a -> b) -> PAlg effs effs' ()

mapVar :: MapAlg '[Var a] '[Var b] a b
mapVar f (Eff (Scp (Var x))) = var (f x)

mapApp :: MapAlg '[App] '[App] a b
mapApp f (Eff (Scp (App (Const m) (Const n)))) = app m n

mapAbs :: MapAlg '[Abs a] '[Abs b] a b
mapAbs f (Eff (Scp (Abs x (Const m)))) = abs (f x) m

mapLet :: MapAlg '[Let a] '[Let b] a b
mapLet f (Eff (Scp (Let x (Const p) (Const q)))) = lett (f x) p q

mapAnn :: MapAlg '[Label t] '[Label u] t u
mapAnn f (Eff (Scp (Label t (Const m)))) = label (f t) m

mapVAAL :: forall a b . (a -> b) -> Term (VAAL a) -> Term (VAAL b)
mapVAAL f = pfold () alg where
    alg :: PAlg (VAAL a) (VAAL b) ()
    alg = mapVar f ## mapApp f ## mapAbs f ## mapLet f



type UniqueEffs a b = '[Fresh Int, Map a b]

uniqueH :: Ord a => Handler (UniqueEffs a b) '[] [S.StateT Int, S.StateT (M.Map a b)] [(,) Int, (,) (M.Map a b)]
uniqueH = (freshState (+1) ||> state (0 :: Int)) |> mapH

new :: Member (Fresh Int) sig => Prog sig Int
new = fresh @Int

type T1 = (String, Maybe (Ty Int))
type T2 = (Int, Ty Int)

type UniqueAlg effs effs'
    = forall oeffs . Members effs' oeffs
    => PAlg effs (UniqueEffs String T2) (Term oeffs)

uniqueVar :: UniqueAlg '[Var T1] '[Var T2]
uniqueVar (Eff (Scp (Var (x, t)))) = do
    k <- lookup @_ @T2 x
    case (k, t) of
        -- Create new name and new type
        (Nothing, Nothing) -> do
            n <- new
            let s = (n, Free n)
            insert @_ @T2 x s
            return (var s)
        -- Create new name, use given type
        (Nothing, Just t') -> do
            n <- new
            let s = (n, t')
            insert x s
            return (var s)
        -- Use already created name and type
        (Just s, Nothing) -> return (var s)
        -- Use already created name but new type
        -- If the types don't unify, this will be caught at type checking time
        (Just (n, _), Just t'') -> return (var (n, t''))


uniqueApp :: UniqueAlg '[App] '[App]
uniqueApp (Eff (Scp (App (Const m) (Const n)))) = do
    m' <- m
    n' <- n
    return (app m' n')

uniqueAbs :: UniqueAlg '[Abs T1] '[Abs T2]
uniqueAbs (Eff (Scp (Abs (x, t) (Const m)))) = do
    n <- new
    let w = case t of
            Nothing -> (n, Free n)
            Just t' -> (n, t')
    m' <- extend x w m
    return (abs w m')

uniqueLet :: UniqueAlg '[Let T1] '[Let T2]
uniqueLet (Eff (Scp (Let (x, t) (Const p) (Const q)))) = do
    p' <- p
    n <- new
    let w = case t of
            Nothing -> (n, Free n)
            Just t' -> (n, t')
    q' <- extend x w q
    return (lett w p' q')

uniqueVAAL :: Term (VAAL String) -> (Int, Term (VAAL Int))
uniqueVAAL p = fmap (mapVAAL fst) . snd . handle uniqueH $ w where
    alg :: UniqueAlg (VAAL T1) (VAAL T2)
    alg = uniqueVar ## uniqueApp ## uniqueAbs ## uniqueLet
    q = mapVAAL (\x -> (x, Nothing)) $ p
    w = pfold @_ @(UniqueEffs String T2) (return ()) (alg @(VAAL T2)) q
