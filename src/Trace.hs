module Trace where

data Trace
    = TEnter String [Trace]
    | TSuccess
    | TFailure

instance Show Trace where
    show (TEnter s ts) = "Entering " ++ s ++ ":\n" ++ unlines (map (\t -> "\t" ++ show t) ts)
    show TSuccess = "Success"
    show TFailure = "Failure"

showTrace :: Trace -> [String]
showTrace (TEnter s ts) = ("Entering " ++ s ++ ":") : (concatMap (map ("\t" ++) . showTrace) ts)
showTrace TSuccess = ["Success"]
showTrace TFailure = ["Failure"]

showTraces :: [Trace] -> String
showTraces = unlines . concatMap showTrace
