module Trace where

data Trace
    = TEnter String [Trace]
    | TSuccess
    | TFailure
    | TCommit
    deriving Eq

instance Show Trace where
    show (TEnter s ts) = "Trying " ++ s ++ ":\n" ++ show ts --unlines (map (\t -> "\t" ++ show t) ts)
    show TSuccess = "Success"
    show TFailure = "Failure"
    show TCommit = "Commit!"

isSingle :: [Trace] -> Bool
isSingle [TSuccess] = True
isSingle [TFailure] = True
isSingle [TCommit]  = True
isSingle _          = False

showTrace :: Trace -> [String]
showTrace (TEnter s ts)
    | isSingle ts = ["Trying " ++ s ++ ": " ++ show (head ts)]
    | otherwise   = ("Trying " ++ s ++ ":") : (concatMap (map ("\t" ++) . showTrace) ts)
showTrace TSuccess = ["Success"]
showTrace TFailure = ["Failure"]
showTrace TCommit = ["Commit!"]

preTrace :: [Trace] -> [Trace]
preTrace (TEnter s ts@(_:_) : qs) = case last ts of
    TFailure -> TEnter s (preTrace ts) : preTrace qs
    _        -> TEnter s (preTrace ts ++ [TSuccess]) : preTrace qs
preTrace (TEnter s [] : qs) = TEnter s [TSuccess] : preTrace qs
preTrace (t:ts) = t : preTrace ts
preTrace [] = []

showTraces :: [Trace] -> String
showTraces = unlines . concatMap showTrace . preTrace
