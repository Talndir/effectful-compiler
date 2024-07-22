{-# LANGUAGE DataKinds #-}
module Parsing.Parser1 where

import Control.Applicative
import Control.Monad (guard, void)
import Data.Char (isAlphaNum)

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.State
import Control.Effect.Cut

import Language.Lambda1

type PSig = [Put String, Get String, Empty, Choose, CutFail, CutCall]

char :: Members PSig sig => Prog sig Char
char = do
    input <- get
    case input of
        [] -> stop
        (x:xs) -> do
            put xs
            return x

satisfy :: Members PSig sig => (a -> Bool) -> Prog sig a -> Prog sig a
satisfy f p = do
    x <- p
    guard (f x)
    return x

whitespace :: Members PSig sig => Prog sig ()
whitespace = void $ many (satisfy (==' ') char)

symbol :: Members PSig sig => Char -> Prog sig Char
symbol c = satisfy (==c) char <* whitespace

ident :: Members PSig sig => Prog sig String
ident = some (satisfy isAlphaNum char) <* whitespace

parens :: Members PSig sig => Prog sig a -> Prog sig a
parens p = symbol '(' *> p <* symbol ')'

term, term', lam, var :: Members PSig sig => Prog sig (Term String)
var = Var <$> ident
lam = do
    symbol '\\'
    -- cut
    x <- ident
    symbol '.'
    t <- term
    return (Lam x t)
term' = parens term <|> lam <|> var
term = term' <* cut >>= termC

termC :: Members PSig sig => Term String -> Prog sig (Term String)
termC t1 = cutCall (    (do t2 <- term'; cut; termC (App t1 t2))
                    <|> (do return t1))

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

parse :: String -> Prog PSig a -> [(String, a)]
parse s = handle (state s |> cutList)

parse1 :: String -> Prog PSig a -> Maybe a
parse1 s = fmap snd . safeHead . parse s
