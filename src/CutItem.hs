{-# LANGUAGE PatternSynonyms #-}

module CutItem where

import Control.Monad (join, ap)
import Control.Applicative (Alternative(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Family (Forward(..))
import Control.Family.Scoped (Scp(..))
import Data.HFunctor (HFunctor(..))

newtype CutItemT m a = CutItemT { runCutItemT :: m (Maybe (Maybe a)) }
    deriving Functor

pattern Result :: a -> Maybe (Maybe a)
pattern Result x = Just (Just x)

pattern Failure, CutFailure :: Maybe (Maybe a)
pattern Failure = Nothing
pattern CutFailure = Just Nothing

{-# COMPLETE Result, Failure, CutFailure #-}

fromCutItemT :: Functor m => CutItemT m a -> m (Maybe a)
fromCutItemT (CutItemT x) = fmap join x

instance Monad m => Applicative (CutItemT m) where
    pure = CutItemT . fmap (Just . Just) . pure
    (<*>) = ap

instance Monad m => Alternative (CutItemT m) where
    empty = CutItemT $ return Failure
    CutItemT mx <|> CutItemT my = CutItemT $ do
        x <- mx
        case x of
            Result r    -> return (Result r)
            Failure     -> my
            CutFailure  -> return CutFailure

instance Monad m => Monad (CutItemT m) where
    CutItemT mx >>= k = CutItemT $ do
        x <- mx
        case x of
            Result r    -> runCutItemT (k r)
            Failure     -> return Failure
            CutFailure  -> return CutFailure

instance MonadTrans CutItemT where
    lift = CutItemT . fmap (Just . Just)

instance Functor f => Forward (Scp f) CutItemT where
    fwd alg (Scp op) = (CutItemT . alg . Scp . fmap runCutItemT) op

instance HFunctor CutItemT where
    hmap h (CutItemT x) = CutItemT (h x)
