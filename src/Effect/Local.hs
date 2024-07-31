{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Effect.Local where

import Control.Effect
import Control.Family.Scoped

type Local = Scp Local'
data Local' a where
    Local :: a -> a -> Local' a
    deriving Functor

local :: Member Local sig => Prog sig a -> Prog sig a -> Prog sig a
local t k = call (Scp (Local (fmap return t) (fmap return k)))
