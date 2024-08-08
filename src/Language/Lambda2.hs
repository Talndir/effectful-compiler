{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Language.Lambda2 where

import Prelude hiding (lookup, abs)

import Data.Kind (Type)
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

data Var a k where
    Var :: a -> Var a k
    deriving Functor

var :: forall a sig . Member (Scp (Var a)) sig => a -> Prog sig ()
var x = call @(Scp (Var a)) (Scp (Var x))

data Abs a k where
    Abs :: a -> k -> Abs a k
    deriving Functor

abs :: forall a b sig . Member (Scp (Abs a)) sig => a -> Prog sig b -> Prog sig b
abs x m = call @(Scp (Abs a)) (Scp (Abs x (fmap return m)))

data App a k where
    App :: k -> k -> App a k
    deriving Functor

app :: forall a b sig . Member (Scp (App a)) sig => Prog sig b -> Prog sig b -> Prog sig b
app m n = call @(Scp (App a)) (Scp (App (fmap return m) (fmap return n)))

data Let a k where
    Let :: a -> k -> k -> Let a k
    deriving Functor

lett :: forall a b sig . Member (Scp (Let a)) sig => a -> Prog sig b -> Prog sig b -> Prog sig b
lett x p q = call @(Scp (Let a)) (Scp (Let x (fmap return p) (fmap return q)))

data Ann t a k where
    Ann :: t -> k -> Ann t a k
    deriving Functor

ann :: forall a b t sig . Member (Scp (Ann t a)) sig => t -> Prog sig b -> Prog sig b
ann t p = call @(Scp (Ann t a)) (Scp (Ann t (fmap return p)))


type family MakeTerm (fs :: [Type -> Signature]) (t :: Type) :: [Effect] where
    MakeTerm '[] t = '[]
    MakeTerm (f ': fs) t = Scp (f t) ': MakeTerm fs t

type Term fs t = Prog (MakeTerm fs t) ()
type Annotated fs t a = Prog (MakeTerm (Ann a ': fs) (t, a)) ()

data FixedType = FInt | FBool
    deriving Eq

instance Show FixedType where
    show FInt = "Int"
    show FBool = "Bool"

data Ty' c a
    = Free a
    | Bound c
    | Fixed FixedType
    | Arr (Ty' c a) (Ty' c a)
    | Forall c (Ty' c a)
    deriving (Eq, Functor, Foldable)

type Ty a = Ty' a a

instance Applicative (Ty' c) where
    pure = Free
    (<*>) = ap

instance Monad (Ty' c) where
    Free x >>= f = f x
    Bound x >>= _ = Bound x
    Fixed x >>= _ = Fixed x
    Arr t1 t2 >>= f = Arr (t1 >>= f) (t2 >>= f)
    Forall x t >>= f = Forall x (t >>= f)

instance (Show c, Show a) => Show (Ty' c a) where
    showsPrec p k = case k of
        Free x -> showString "'" . shows x
        Bound x -> shows x
        Fixed x -> shows x
        Arr t1 t2 ->
            showParen (p > arrPrec)
            ( showsPrec (arrPrec + 1) t1
            . showString " -> "
            . showsPrec arrPrec t2)
        Forall x t -> showForall [x] t
        where
            arrPrec = 10

            showForall :: [c] -> Ty' c a -> ShowS
            showForall xs (Forall x t) = showForall (x:xs) t
            showForall xs t = showString "∀ " . f (reverse xs) . showString " . " . shows t

            f xs = foldl (.) id . intersperse (showString " ") . map shows $ xs


type VAA = [Var, App, Abs]
type VAAL = [Var, App, Abs, Let]

type ShowAlg effs a
    = forall (x :: Type)
    .  Effs (MakeTerm effs a) (Const (Int -> ShowS)) (Const (Int -> ShowS) x)
    -> Const (Int -> ShowS) x

showVar :: Show a => ShowAlg '[Var] a
showVar (Eff (Scp (Var x))) = Const $ \_ -> shows x

showApp :: Show a => ShowAlg '[App] a
showApp (Eff (Scp (App (Const m) (Const n)))) = Const $ \p -> 
    showParen (p > 10)
    ( m 10
    . showString " "
    . n 11)

showAbs :: Show a => ShowAlg '[Abs] a
showAbs (Eff (Scp (Abs x (Const m)))) = Const $ \p ->
    showParen (p > 5)
    ( showString "λ "
    . shows x
    . showString " . "
    . m 0)

showLet :: Show a => ShowAlg '[Let] a
showLet (Eff (Scp (Let x (Const m) (Const n)))) = Const $ \p ->
    showParen (p > 5)
    ( showString "let "
    . shows x
    . showString " = "
    . m 0
    . showString " in "
    . n 0)

showAnn :: (Show t, Show a) => ShowAlg '[Ann t] a
showAnn (Eff (Scp (Ann t (Const m)))) = Const $ \p ->
    showParen True
    ( shows t
    . showString " :: "
    . m 0 )

showVAAL :: forall a . Show a => Term VAAL a -> String
showVAAL p = unConst (fold alg (\_ -> undefined) p) 0 "\n" where
    alg :: ShowAlg VAAL a
    alg = showVar @a ## showApp @a ## showAbs @a ## showLet @a


type MapAlg effs effs' a b
    = (a -> b) -> CAlgebra (MakeTerm effs a) (MakeTerm effs' b) ()

type Mapper effs a b
    = forall effs' . Members (MakeTerm effs b) (MakeTerm effs' b)
    => MapAlg effs effs' a b

mapVar :: Mapper '[Var] a b
mapVar f (Eff (Scp (Var x))) = Const $ var (f x)

mapApp :: forall a b . Mapper '[App] a b
mapApp f (Eff (Scp (App (Const m) (Const n)))) = Const $ app @b m n

mapAbs :: forall a b . Mapper '[Abs] a b
mapAbs f (Eff (Scp (Abs x (Const m)))) = Const $ abs (f x) m

mapLet :: forall a b . Mapper '[Let] a b
mapLet f (Eff (Scp (Let x (Const p) (Const q)))) = Const $ lett (f x) p q

mapAnn :: forall a b t . Mapper '[Ann t] a b
mapAnn f (Eff (Scp (Ann t (Const m)))) = Const $ ann @b t m

mapVAAL :: (a -> b) -> Term VAAL a -> Term VAAL b
mapVAAL f = cfold (alg f) () where
    alg g = (mapVar @_ @_ @VAAL g) ## (mapApp @_ @_ @VAAL g) ## (mapAbs @_ @_ @VAAL g) ## (mapLet @_ @_ @VAAL g)


type UniqueEffs a b = '[Fresh Int, Map a b]

uniqueH :: Ord a => Handler (UniqueEffs a b) '[] [S.StateT Int, S.StateT (M.Map a b)] [(,) Int, (,) (M.Map a b)]
uniqueH = (freshState (+1) ||> state (0 :: Int)) |> mapH

new :: Eq a => Prog (UniqueEffs a Int) Int
new = fresh @Int

type UniqueAlg effs effs' a b
    = CAlgebra (MakeTerm effs a) (UniqueEffs a b) (Term effs' b)

type Uniquer effs a b
    =  forall effs' . Members (MakeTerm effs b) (MakeTerm effs' b)
    => UniqueAlg effs effs' a b

uniqueApp :: Uniquer '[App] String Int
uniqueApp (Eff (Scp (App (Const m) (Const n)))) = Const $ do
    m' <- m
    n' <- n
    return (app @Int m' n')

uniqueAbs :: Uniquer '[Abs] String Int
uniqueAbs (Eff (Scp (Abs x (Const m)))) = Const $ do
    w <- new
    m' <- extend x w m
    return (abs w m')

uniqueVar :: Uniquer '[Var] String Int
uniqueVar (Eff (Scp (Var x))) = Const $ do
    t <- lookup @_ @Int x
    case t of
        Just t' -> return (var t')
        Nothing -> do
            w <- new
            insert x w
            return (var w)

uniqueLet :: Uniquer '[Let] String Int
uniqueLet (Eff (Scp (Let x (Const p) (Const q)))) = Const $ do
    p' <- p
    w <- new
    q' <- extend x w q
    return (lett w p' q')

uniqueVAAL :: Term VAAL String -> (Int, Term VAAL Int)
uniqueVAAL = snd . handle uniqueH . cfold alg (return ()) where
    alg = (uniqueVar @VAAL) ## (uniqueApp @VAAL) ## (uniqueAbs @VAAL) ## (uniqueLet @VAAL)




