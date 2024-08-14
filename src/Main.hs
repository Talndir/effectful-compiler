module Main where

import Parsing.Parser3
import Typing.Typer3
import Language.Lambda2

expr :: String
expr = "\\x . \\ y . (x y ((\\ t . (\\ w . w) x) y) ((\\ u . u) y))"

term1 :: Term (VAAL T)
term1 = let Just (_, k) = parse expr termP in k

term2 :: Term (VAAL String)
term2 = mapVAAL fst term1

term3 :: Term (VAAL String)
term3 = opt @String term2

--term2 :: (Int, Term (VAAL Int))
--term2 = uniqueVAAL term1

--term3 :: Term VAAL (Int, Ty Int)
--term3 :: Either String (String, Ty Int, [(Int, Ty Int)], Int)
--term3 = uncurry typeIt' term2

main :: IO ()
main = putStrLn "Hello, Haskell!"

