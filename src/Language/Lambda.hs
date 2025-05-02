{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Lambda where

{------------------------------------------------------------------------------
    This module defines the syntax of the polymorphic lambda calculus
    as a number of effects. It also implements handlers for substitution
    and pretty-printing.
------------------------------------------------------------------------------}

import Prelude hiding (lookup, abs)

import Control.Monad
import qualified Control.Monad.Trans.State.Strict as S
import Data.List (intersperse)
import qualified Data.Map as M

import Control.Effect
import Control.Family.Scoped
import Control.Effect.State
import Data.List.Kind

import Stuff
import Effect.Map
import Effect.Fresh
import Effect.Label

import Data.HFunctor

{--- LANGUAGE DEFINITION ---}

{- 
    Each piece of syntax consists of:
        * The operation itself as a scoped effect.
        * A smart constructor.
        * A pattern for extracting the subprogram(s).
        * A pattern for extracting the subeffect(s).
-}

type Pos = (Int, Int)

-- Variables
type Var a = Scp (Var' a)
data Var' a k where
    Var :: a -> Var' a k
    deriving Functor

var :: forall a b sig . Member (Var a) sig => a -> Prog sig b
var x = call @(Var a) (Scp (Var x))

pattern Var' :: forall a sig b . Member (Var a) sig => a -> Prog sig b
pattern Var' x <- (Call (prj @(Var a) -> Just (Scp (Var x))) _ _)

pattern CVar :: forall a sig b c . Member (Var a) sig => a -> Effs sig (Const b) c
pattern CVar x <- (prj @(Var a) -> Just (Scp (Var x)))

-- Abstractions
type Abs a = Scp (Abs' a)
data Abs' a k where
    Abs :: a -> k -> Abs' a k
    deriving Functor

abs :: forall a b sig . Member (Abs a) sig => a -> Prog sig b -> Prog sig b
abs x m = call @(Abs a) (Scp (Abs x (fmap return m)))

pattern Abs' :: forall a sig b . Member (Abs a) sig => a -> Prog sig b -> Prog sig b
pattern Abs' x p <- (prj2 @(Abs a) -> Just (Scp (Abs x (join -> p))))

pattern CAbs :: forall a sig b c . Member (Abs a) sig => a -> b -> Effs sig (Const b) c
pattern CAbs x m <- (prj @(Abs a) -> Just (Scp (Abs x (unConst -> m))))

-- Applications
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

-- Let-bindings
type Let a = Scp (Let' a)
data Let' a k where
    Let :: a -> k -> k -> Let' a k
    deriving Functor

lett :: forall a b sig . Member (Let a) sig => a -> Prog sig b -> Prog sig b -> Prog sig b
lett x p q = call @(Let a) (Scp (Let x (fmap return p) (fmap return q)))

pattern Let' :: forall a sig b . Member (Let a) sig => a -> Prog sig b -> Prog sig b -> Prog sig b
pattern Let' x m n <- (prj2 @(Let a) -> Just (Scp (Let x (join -> m) (join -> n))))

pattern CLet :: forall a sig b c . Member (Let a) sig => a -> b -> b -> Effs sig (Const b) c
pattern CLet x m n <- (prj @(Let a) -> Just (Scp (Let x (unConst -> m) (unConst -> n))))

{--- TYPES ---}

{-
    The types are a bit weird - they are defined like this so they form a monad
    such that substitution is monadic bind.
-}

-- Concrete types
data FixedType = FInt | FBool
    deriving Eq

instance Show FixedType where
    show FInt = "Int"
    show FBool = "Bool"

-- The data structure for types
-- `c` is the type of bound variables, `a` is the type of free variables.
data Ty' c a
    = TFree a                           -- Free variables
    | TBound c                          -- Bound variables
    | TFixed FixedType                  -- Concrete types
    | TArr (Ty' c a) (Ty' c a)          -- Function type
    | TForall c (Ty' c a)               -- Forall type
    deriving (Eq, Functor, Foldable)

-- In reality, we always have `c ~ a`
newtype Ty a = Ty { unTy :: Ty' a a }
    deriving Eq

instance Show a => Show (Ty a) where
    show (Ty x) = show x

-- These are just common operations lifted to `Ty`

-- Free variable substitution, i.e. `>>=`
(#$) :: (a -> Ty a) -> Ty a -> Ty a
(#$) f (Ty x) = Ty (x >>= unTy . f)

-- Composition of substitutions, i.e. Kleisli composition
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

-- Substitution only changes the free variables
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


{--- Term substitution ---}

{-
    To implement term substitution modularly, a type class is defined that
    describes how each individual component works under substitution. Another
    type class inductively combines them together. Simply pass the correct
    type and the substituter is automatically assembled.
-}

-- Our language
type VAAL a = [Var a, App, Abs a, Let a]

-- Terms are syntax trees without values
-- This is because variables are represented as an operation
type Term effs = Prog effs ()

-- A substitution algebra replaces a variable `a` with a term `Term oeffs`
type SubstAlg a effs
    =  forall oeffs . Members effs oeffs
    => a -> Term oeffs -> CAlg effs (Term oeffs)

-- A substitution is a function that takes a variable and a term and
-- tries to replace that variable with that term inside another term
type Subst a effs
    = a -> Term effs -> Term effs -> Term effs

-- A class describing how a single operation is substituted into
class SubstA a eff where
    substAlg :: SubstAlg a '[eff]

-- The same, but for a list of effects
class SubstA' a effs where
    substAlg' :: SubstAlg a effs

-- Base case
instance SubstA' a '[] where
    substAlg' _ _ = absurdEffs

-- Inductive case
instance (SubstA a eff, SubstA' a effs, HFunctor eff, KnownNat (Length effs)) => SubstA' a (eff ': effs) where
    substAlg' v p = substAlg v p ## substAlg' v p where

-- The actual implementation
instance Eq a => SubstA a (Var a) where
    substAlg v p (CVar x)
        | x == v = p
        | otherwise = var x

instance SubstA a App where
    substAlg _ _ (CApp m n) = app m n

instance SubstA a (Abs a) where
    substAlg _ _ (CAbs (x :: a) m) = abs x m

instance SubstA a (Let a) where
    substAlg _ _ (CLet (x :: a) m n) = lett x m n

-- Combining them all - it's easy peasy!
substVAAL :: forall a . Eq a => Subst a (VAAL a)
substVAAL v p = cfold (return ()) (substAlg' @a @(VAAL a) v p)


{--- SMALL-STEP REDUCTION ---}

{-
    To perform small-step reduction, we manually recurse through the syntax
    tree, i.e. we simulate a shallow handler. This gets a little complex due
    to making the entire thing modular over any combination of effects. The
    fact that the operations are scoped does not actually change the deepness
    of the handling. Manual recursion is required because we are implementing
    call-by-name semantics, which does NOT reduce the right-hand side of an
    application before performing the substitution.

    The result of `Maybe (Term effs)` everywhere is used as follows:
        * `Just e` means `e` is the next step in reduction.
        * `Nothing` means the term could not reduce any further.
-}

-- A `Reduce'` takes an environment (the `Subst`) and a reducer and creates
-- a new reducer that performs the substitution when encountering variables.
type Reduce' a effs'
    = Subst a effs'
    -> (Term effs' -> Maybe (Term effs'))
    -> Term effs' -> Maybe (Term effs')

type Reduce a effs
    =  forall effs' . Members effs effs'
    => Reduce' a effs'

-- The reduction rules for applications. Note how manual recursion is used
-- to force the reduction of the left argument before the right argument.
reduceApp :: Eq a => Reduce a '[App, Abs a]
reduceApp f _ (App' (Abs' (x :: a) m) n) = Just (f x n m)
reduceApp _ g (App' m n) = case g m of
    Just m' -> Just (app m' n)
    Nothing -> case g n of
        Just n' -> Just (app m n')
        Nothing -> Nothing
reduceApp _ _ _ = Nothing

-- Let is simpler
reduceLet :: Eq a => Reduce a '[Let a]
reduceLet f _ (Let' (x :: a) m n) = Just (f x m n)
reduceLet _ _ _ = Nothing

-- This chains two possibly failing computations,
-- taking the first that succeeds
(>~>) :: (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
(>~>) f g x = maybe (g x) Just (f x)

-- This is where the fun begins!
-- We sequence all the individual reducers (i.e. the different reduction rules)
-- in order. However, we also need to pass the entire reducer currently under
-- construction to each separate part, so that they can correctly reduce subterms.
-- Reduction of subterms is identical to reduction of overall terms, as we're just
-- reducing in evaluation contexts (also called the frame rule).
makeReducer :: Subst a effs -> [Reduce' a effs] -> Term effs -> Maybe (Term effs)
makeReducer s rs = r where
    r = foldl (\f g -> f >~> g s r) (const Nothing) rs

reduceVAAL :: forall a . Eq a => Term (VAAL a) -> Maybe (Term (VAAL a))
reduceVAAL = makeReducer substVAAL [reduceApp, reduceLet]

iterM :: (a -> Maybe a) -> a -> [a]
iterM f x = case f x of
    Nothing -> [x]
    Just y -> x : iterM f y

-- Returns the sequence of reductions of a term, down to normal form.
-- Thanks to strong normalization, this is always finite!
exec :: Eq a => Term (VAAL a) -> [Term (VAAL a)]
exec = iterM reduceVAAL


{--- PEEPHOLE OPTIMISATION ---}

{- A simple example of optimising out identity functions -}

ff :: Injects effs effs' => a -> Effs effs (Const (Prog effs' a)) x -> Prog effs' a
ff x eff = Call (injs eff) (fmap (const undefined) . unConst) (const (return x))

optId :: forall a effs . (Eq a, Members '[Var a, Abs a, App] effs, Injects effs effs)
    => CAlg effs (Term effs)
optId (CApp (Abs' (x :: a) (Var' y)) n)
    | x == y = n
    | otherwise = var y
optId op = ff () op

opt :: forall a effs . (Eq a, Members '[Var a, Abs a, App] effs, Injects effs effs) => Term effs -> Term effs
opt op = cfold (return ()) (optId @a) op


{--- PRETTY-PRINTING ---}

{- Like reduction, this can easily be made modular with type classes. -}

instance Show a => ShowA (Var a) where
    showAlg (Eff (Scp (Var x))) = \_ -> shows x

instance Show a => ShowA (Abs a) where
    showAlg (CAbs (x :: a) m) = \p ->
        showParen (p > 5)
        ( showString "λ "
        . shows x
        . showString " . "
        . m 0)

instance ShowA App where
    showAlg (Eff (Scp (App (Const m) (Const n)))) = \p -> 
        showParen (p > 10)
        ( m 10
        . showString " "
        . n 11)

instance Show a => ShowA (Let a) where
    showAlg (Eff (Scp (Let x (Const m) (Const n)))) = \p ->
        showParen (p > 5)
        ( showString "let "
        . shows x
        . showString " = "
        . m 0
        . showString " in "
        . n 0)

instance Show a => ShowA (Label a) where
    showAlg (Eff (Scp (Label t (Const m)))) = \p ->
        showParen True
        ( shows t
        . showString " :: "
        . m 0 )


{--- HELPERS: MAP AND UNIQUE NAMING ---}

{-
    Just like above, type classes can be used to define these operations
    modularly. We define the standard functor-style map, as well as a
    way of uniquely renaming variables using a `Map` effect, which exposes
    an interface for a key-value store.
-}

type MapAlg effs effs' a b
    = (a -> b) -> PAlg effs effs' ()

class MapA' effs effs' a b where
    mapAlg' :: MapAlg effs effs' a b

class MapA eff eff' a b where
    mapAlg :: MapAlg '[eff] '[eff'] a b

instance MapA' '[] '[] a b where
    mapAlg' _ = absurdEffs

instance (  MapA eff eff' a b, MapA' effs effs' a b,
            HFunctor eff, HFunctor eff',
            KnownNat (Length effs))
    => MapA' (eff : effs) (eff' : effs') a b where
    mapAlg' :: MapAlg (eff : effs) (eff' : effs') a b
    mapAlg' f = mapAlg @eff @eff' f ## mapAlg' @effs @effs' f


type LVAAL t a = [Label t, Var a, App, Abs a, Let a]

instance MapA (Var a) (Var b) a b where
    mapAlg f (Eff (Scp (Var x))) = var (f x)

instance MapA App App a b where
    mapAlg _ (CApp m n) = app m n

instance MapA (Abs a) (Abs b) a b where
    mapAlg f (CAbs x m) = abs (f x) m

instance MapA (Let a) (Let b) a b where
    mapAlg f (CLet x p q) = lett (f x) p q

instance MapA (Label t) (Label u) t u where
    mapAlg f (Eff (Scp (Label t (Const m)))) = label (f t) m

mapVAAL :: forall a b . (a -> b) -> Term (VAAL a) -> Term (VAAL b)
mapVAAL f = pfold () (mapAlg' @(VAAL a) @(VAAL b) f) where

mapLVAAL :: forall a b t . (a -> b) -> Term (LVAAL t a) -> Term (LVAAL t b)
mapLVAAL f = pfold () (alg) where
    alg :: PAlg (Label t ': VAAL a) (Label t ': VAAL b) ()
    alg = mapAlg @_ @(Label t) @_ @t id ## mapAlg' @_ @(VAAL b) f


type UniqueEffs a b = '[Fresh Int, Map a b]

uniqueH :: Ord a => Handler (UniqueEffs a b) '[] [S.StateT Int, S.StateT (M.Map a b)] [(,) Int, (,) (M.Map a b)]
uniqueH = (freshState (+1) ||> state (0 :: Int)) |> mapH

new :: Member (Fresh Int) sig => Prog sig Int
new = fresh @Int

type T1 = (String, Maybe (Ty Int))
type T2 = (String, Int, Ty Int)

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
            let s = (x, n, Free n)
            insert @_ @T2 x s
            return (var s)
        -- Create new name, use given type
        (Nothing, Just t') -> do
            n <- new
            let s = (x, n, t')
            insert x s
            return (var s)
        -- Use already created name and type
        (Just s, Nothing) -> return (var s)
        -- Use already created name but new type
        -- If the types don't unify, this will be caught at type checking time
        (Just (_, n, _), Just t'') -> return (var (x, n, t''))


uniqueApp :: UniqueAlg '[App] '[App]
uniqueApp (Eff (Scp (App (Const m) (Const n)))) = do
    m' <- m
    n' <- n
    return (app m' n')

uniqueAbs :: UniqueAlg '[Abs T1] '[Abs T2]
uniqueAbs (Eff (Scp (Abs (x, t) (Const m)))) = do
    n <- new
    let w = case t of
            Nothing -> (x, n, Free n)
            Just t' -> (x, n, t')
    m' <- extend x w m
    return (abs w m')

uniqueLet :: UniqueAlg '[Let T1] '[Let T2]
uniqueLet (Eff (Scp (Let (x, t) (Const p) (Const q)))) = do
    p' <- p
    n <- new
    let w = case t of
            Nothing -> (x, n, Free n)
            Just t' -> (x, n, t')
    q' <- extend x w q
    return (lett w p' q')

uniqueAnn :: UniqueAlg '[Label t] '[Label t]
uniqueAnn (Eff (Scp (Label x (Const p)))) = do
    p' <- p
    return (label x p')

uniqueVAAL :: Term (VAAL String) -> (Int, Term (VAAL (String, Int)))
uniqueVAAL p = fmap (mapVAAL (\(n, k, _) -> (n, k))) . snd . handle uniqueH $ w where
    alg :: UniqueAlg (VAAL T1) (VAAL T2)
    alg = uniqueVar ## uniqueApp ## uniqueAbs ## uniqueLet
    q = mapVAAL (\x -> (x, Nothing)) $ p
    w = pfold @_ @(UniqueEffs String T2) (return ()) (alg @(VAAL T2)) q

uniqueLVAAL :: forall t . Term (Label t ': VAAL String) -> (Int, Term (Label t ': VAAL (String, Int)))
uniqueLVAAL p = fmap (mapLVAAL (\(n, k, _) -> (n, k))) . snd . handle uniqueH $ w where
    alg :: UniqueAlg (Label t ': VAAL T1) (Label t ': VAAL T2)
    alg = uniqueAnn ## uniqueVar ## uniqueApp ## uniqueAbs ## uniqueLet
    q = mapLVAAL (\x -> (x, Nothing)) $ p
    w = pfold @_ @(UniqueEffs String T2) (return ()) (alg @(Label t ': VAAL T2)) q
