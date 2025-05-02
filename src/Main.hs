{-# LANGUAGE DataKinds #-}
module Main where

import Parsing.Parser
import Typing.Typer
import Language.Lambda
import Effect.Label
import Trace
import Control.Effect

expr :: String
expr = "(\\ f . \\ x . x x)"

term1 :: Term (Label Pos ': VAAL (String, Maybe (Ty String)))
term1 = let Just (_, k) = parse termP expr in k

term2 :: (Int, Term (Label Pos ': VAAL (String, Int)))
term2 = uniqueLVAAL (mapLVAAL fst term1)

pterm2 :: IO ()
pterm2 = putStr (show . snd $ term2)

test :: Show a => Prog PSig (Term (Label Pos : VAAL a)) -> String -> IO ()
test p s = let (tr, r) = parseH p s in do
    putStrLn (showTraces tr)
    case r of
        Nothing -> return ()
        Just (_, q) -> putStrLn (show q)

tterm :: IO ()
tterm = test termP expr

term3 :: IO ()
term3 = case fmap show . uncurry (typer expr) $ term2 of
    Left x -> putStrLn x
    Right x -> putStr x

main :: IO ()
main = putStrLn "Hello, Haskell!"

