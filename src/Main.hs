module Main where

import Parsing.Parser2
import Typing.Typer1
import Language.Lambda1

expr :: String
expr = "\\ x . \\ z . (\\ f . f x) z w"

term1 :: Term String
term1 = let Just (_, k) = parse expr term in k

term2 :: Term (Int, Ty Int)
term2 = rename term1

term3 :: Term (Int, Ty Int)
term3 = typeIt term2

main :: IO ()
main = putStrLn "Hello, Haskell!"

