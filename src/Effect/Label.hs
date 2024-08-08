{-# LANGUAGE DataKinds #-}
module Effect.Label where

import Control.Effect
import Control.Family.Scoped

type Label t = Scp (Label' t)
data Label' t a where
    Label :: t -> a -> Label' t a
    deriving Functor

label :: Member (Label t) sig => t -> Prog sig a -> Prog sig a
label t p = call (Scp (Label t (fmap return p)))

labelAlgIgnore
    :: forall m oeffs t . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs '[Label t] m x -> m x)
labelAlgIgnore _ op
    | Just (Scp (Label _ p)) <- prj @(Label t) op = p

labelIgnore :: Handler '[Label t] '[] '[] '[]
labelIgnore = interpretM labelAlgIgnore
