{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Parsing.Parser2 where

import Control.Applicative
import Control.Monad (void)
import Data.Char (isAlphaNum)

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.State
import Control.Effect.Cut
import Control.Effect.Writer

import Control.Family.Algebraic
import Control.Family.Scoped

import Language.Lambda1
import CutItem
import Effect.Label
import Stuff

type Satisfy c = Alg (Satisfy' c)
data Satisfy' c a where
    Satisfy :: (c -> Bool) -> (c -> a) -> Satisfy' c a
    deriving Functor

satisfy :: Member (Satisfy c) sig => (c -> Bool) -> Prog sig c
satisfy p = call (Alg (Satisfy p return))

satisfyAlg
    :: forall m oeffs c . (Monad m, Members [Put [c], Get [c], Empty] oeffs)
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs '[Satisfy c] m x -> m x)
satisfyAlg oalg op
    | Just (Alg (Satisfy p k)) <- prj @(Satisfy c) op = eval oalg $ do
        (x:xs) <- get
        if not (p x) then stop else do
            put xs
            return (k x)

satisfyState :: Handler '[Satisfy c] [Put [c], Get [c], Empty] '[] '[]
satisfyState = interpretM satisfyAlg


type Commit = Alg Commit'
data Commit' a where
    Commit :: a -> Commit' a
    deriving Functor

commit :: Member Commit sig => Prog sig ()
commit = call (Alg (Commit (return ())))

type Tag = (String, Bool, Bool)
type Trace = String
type PSig = [Satisfy Char, Label Tag, Empty, Choose, Commit, CutCall]

trace :: Member (Tell Trace) sig => String -> Prog sig ()
trace = tell @Trace

whitespace :: Members PSig sig => Prog sig ()
whitespace = void $ many (satisfy (==' '))

symbol :: Members PSig sig => Char -> Prog sig Char
symbol c = satisfy (==c) <* whitespace

ident :: Members PSig sig => Prog sig String
ident = some (satisfy isAlphaNum) <* whitespace

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
term = term' <* commit >>= termC

termC :: Members PSig sig => Term String -> Prog sig (Term String)
termC t1 = cutCall (    (do t2 <- term'; commit; termC (App t1 t2))
                    <|> (do return t1))

makeTrace
    :: Prog [Label Tag, Empty, Choose, Commit, CutCall] a
    -> Prog [Empty, Choose, Commit, CutCall, Tell Trace] a
makeTrace = eval f where
    f :: Algebra [Label Tag, Empty, Choose, Commit, CutCall]
        (Prog [Empty, Choose, Commit, CutCall, Tell Trace])
    f op
        | Just (Scp (Label t k))    <- prj @(Label Tag) op = do
            k
        | Just (Alg Empty)          <- prj op = do
            --trace "FAILURE"
            empty
        | Just (Scp (Choose x y))   <- prj op = x <|> y
        | Just (Alg (Commit x))     <- prj op = do
            --trace ""
            commit
            return x
        | Just (Scp (CutCall x))    <- prj op = do
            cutCall x
        | otherwise                           = undefined

type Sig1 = [Label Tag, Empty, Choose, Commit, CutCall]
type Sig2 = [Empty, Choose, Commit, CutCall, Tell Trace]

mtH :: Handler Sig1 Sig2 '[] '[]
mtH = interpretM f where
    f :: forall m . Monad m
      => (forall x . Effs Sig2 m x -> m x)
      -> (forall x . Effs Sig1 m x -> m x)
    f oalg op
        | Just (Scp (Label (n, _, _) k))    <- prj @(Label Tag) op = do
            x <- k
            eval oalg $ do
                trace ("Entering " ++ n)
                return x
        | Just (Alg Empty)          <- prj op = eval oalg $ do
            trace "FAILURE"
            empty
        | Just (Scp (Choose mx my))   <- prj op = oalg $ inj (Scp (Choose mx my))
        | Just (Alg (Commit x))     <- prj op = eval oalg $ do
            trace "COMMIT"
            commit
            return x
        | Just (Scp (CutCall mx))    <- prj op = do
            x <- mx
            eval oalg $ do
                cutCall (return x)
        | otherwise                           = undefined
    

cutItemAlg :: Monad m
    => (Algebra oeffs m)
    -> (Algebra [Empty, Choose, Commit, CutCall] (CutItemT m))
cutItemAlg _ op
    | Just (Alg Empty)          <- prj op = empty
    | Just (Scp (Choose x y))   <- prj op = x <|> y
    | Just (Alg (Commit x))     <- prj op = return x <|> CutItemT (return CutFailure)
    | Just (Scp (CutCall x))    <- prj op = cutAlg x
    | otherwise                           = undefined
    where
        cutAlg (CutItemT mx) = CutItemT $ do
            x <- mx
            case x of
                CutFailure -> return Failure
                _          -> return x

cutItem :: Handler [Empty, Choose, Commit, CutCall] '[] '[CutItemT] '[Maybe]
cutItem = handler fromCutItemT cutItemAlg

parse :: String -> Prog PSig a -> Maybe (String, a)
parse s = handle (satisfyState `pipe` state s |> labelIgnore |> cutItem)

parseT :: String -> Prog PSig a -> (String, Maybe (String, a))
parseT s = handle ((satisfyState ||> state s) |> (mtH ||> (cutItem |> writer)))
