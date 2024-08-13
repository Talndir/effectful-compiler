{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Stuff where

import Control.Monad
import Control.Monad.Trans.Except as E
import Data.Kind (Type)

import Control.Effect
import Control.Family.Algebraic
import Control.Effect.Except
import Data.List.Kind
import Data.HFunctor

newtype Const a x = Const { unConst :: a }
    deriving (Eq, Show, Ord, Functor)

constMap :: (a -> b) -> Const a t -> Const b t
constMap f (Const x) = Const (f x)

type CAlg effs a
    = forall (x :: Type) . Effs effs (Const a) x -> a

type PAlg effs oeffs a
    =  forall oeffs' . Members oeffs oeffs'
    => CAlg effs (Prog oeffs' a)

cfold :: a -> CAlg effs a -> Prog effs b -> a
cfold gen _   (Return _) = gen
cfold gen alg (Call op hk k) = alg
    ((fmap (Const . cfold gen alg . k) . hmap (Const . cfold gen alg . hk)) op)

pfold :: forall effs oeffs a b . Members oeffs oeffs
    => a -> PAlg effs oeffs a -> Prog effs b -> Prog oeffs a
pfold gen alg = cfold (return gen) (alg @oeffs)

instance Monoid a => Applicative (Const a) where
    pure = Const . mempty
    (<*>) = ap

instance Monoid a => Monad (Const a) where
    Const x >>= _ = Const x

instance Semigroup a => Semigroup (Prog effs a) where
    (<>) = liftA2 (<>)

instance Monoid a => Monoid (Prog effs a) where
    mempty = return mempty


(##) :: forall xs ys f a b . KnownNat (Length ys)
     => (Effs xs f a -> b) -> (Effs ys f a -> b) -> (Effs (xs :++ ys) f a -> b)
(##) = heither

(###) :: forall x1 x2 y1 y2 xs ys .
    ( xs ~ x1 `Union` x2
    , ys ~ y1 `Union` y2
    , Injects x1 xs
    , Injects x2 xs
    , Injects (y2 :\\ y1) y2
    , KnownNat (Length y1)
    , KnownNat (Length (y2 :\\ y1))
    )
    => (forall m . Monad m => Algebra x1 m -> Algebra y1 m)
    -> (forall m . Monad m => Algebra x2 m -> Algebra y2 m)
    -> (forall m . Monad m => Algebra xs m -> Algebra ys m)
(###) alg1 alg2 oalg = hunion (alg1 (weakenAlg oalg)) (alg2 (weakenAlg oalg))


prj2 :: forall sig sigs a . (Member sig sigs, HFunctor sig)
    => Prog sigs a -> Maybe (sig (Prog sigs) (Prog sigs a))
prj2 (Return _) = Nothing
prj2 (Call op hk k) = do
    s <- prj @sig op
    let w = fmap k $ hmap hk s
    return w


throwAlg :: Monad m
    => (forall x. oeff m x -> m x)
    -> (forall x. Effs '[Throw e] (E.ExceptT e m) x -> E.ExceptT e m x)
throwAlg _ (Eff (Alg (Throw e))) = E.ExceptT (return (Left e))

throwT :: Handler '[Throw e] '[] '[E.ExceptT e] '[Either e]
throwT = handler E.runExceptT throwAlg
