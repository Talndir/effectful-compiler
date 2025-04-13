{-# LANGUAGE DataKinds #-}
module Main where

import Parsing.Parser4
import Typing.Typer4
import Language.Lambda2
import Effect.Label
import Trace

expr :: String
expr = "(\\ f . \\ x . x x)"

term1 :: Term (Label Pos ': VAAL (String, Maybe (Ty String)))
term1 = let Just (_, k) = parse termP expr in k

term2 :: (Int, Term (Label Pos ': VAAL (String, Int)))
term2 = uniqueLVAAL (mapLVAAL fst term1)

pterm2 :: IO ()
pterm2 = putStr (show . snd $ term2)

tterm :: IO ()
tterm = let (tr, p) = parseH termP expr in do
    putStrLn (showTraces tr)
    case p of
        Nothing -> return ()
        Just (_, q) -> putStrLn (show q)

term3 :: IO ()
term3 = case fmap show . uncurry (typer expr) $ term2 of
    Left x -> putStrLn x
    Right x -> putStr x

main :: IO ()
main = putStrLn "Hello, Haskell!"

