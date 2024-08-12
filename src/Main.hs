module Main where

import Parsing.Parser3
import Typing.Typer3
import Language.Lambda2

expr :: String
expr = "\\ f :: A -> B . let w :: C = f in \\ x :: A . (w :: B) x"

term1 :: Term (VAAL T)
term1 = let Just (_, k) = parse expr termP in k

--term2 :: (Int, Term (VAAL Int))
--term2 = uniqueVAAL term1

--term3 :: Term VAAL (Int, Ty Int)
--term3 :: Either String (String, Ty Int, [(Int, Ty Int)], Int)
--term3 = uncurry typeIt' term2

main :: IO ()
main = putStrLn "Hello, Haskell!"

