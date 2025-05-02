{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Parsing.Parser where

{------------------------------------------------------------------------------
    This module implements a parser for the language. It uses a number of
    standard and non-standard effects. It additionally augments the parser
    with a parsing trace.
------------------------------------------------------------------------------}

import Prelude hiding (abs, log)
import Control.Applicative
import Control.Monad
import Data.Char (isAlphaNum)
import qualified Control.Monad.Trans.State.Strict as Strict

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.State
import Control.Effect.Cut
import Control.Effect.Writer

import Control.Family.Algebraic
import Control.Family.Scoped

import Language.Lambda
import CutItem
import Effect.Label
import Trace

{--- PARSER DSL ---}

{-
    Here we define the DSL for the parser. The three effects are
        * Satisfy: Try to parse a character satisfying a predicate.
        * Commit: Commit to a branch.
        * GetLoc: Get positional information of the current character.
-}

type Satisfy c = Alg (Satisfy' c)
data Satisfy' c a where
    Satisfy :: (c -> Bool) -> (c -> a) -> Satisfy' c a
    deriving Functor

satisfy :: Member (Satisfy c) sig => (c -> Bool) -> Prog sig c
satisfy p = call (Alg (Satisfy p return))

type Commit = Alg Commit'
data Commit' a where
    Commit :: a -> Commit' a
    deriving Functor

commit :: Member Commit sig => Prog sig ()
commit = call (Alg (Commit (return ())))

type GetLoc = Alg GetLoc'
data GetLoc' a where
    GetLoc :: (Int -> a) -> GetLoc' a
    deriving Functor

getLoc :: Member GetLoc sig => Prog sig Int
getLoc = call (Alg (GetLoc return))

-- This algebra interprets Satisfy and GetLoc into state effects (Get and Put)
-- that contain the input as a list of characters and the current position.
satisfyAlg
    :: forall m oeffs c . (Monad m, Members [Put ([c], Int), Get ([c], Int), Empty] oeffs)
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs '[Satisfy c, GetLoc] m x -> m x)
satisfyAlg oalg op
    | Just (Alg (Satisfy p k)) <- prj @(Satisfy c) op = eval oalg $ do
        (input, n :: Int) <- get
        case input of
            [] -> stop
            (x:xs) -> do
                case p x of
                    False -> stop
                    True -> do
                        put (xs, n + 1)
                        return (k x)
    | Just (Alg (GetLoc k)) <- prj @GetLoc op = do
        (_, n :: Int) <- eval oalg $ get @([c], Int)
        return (k n)
    | otherwise = undefined

satisfyState :: Handler '[Satisfy c, GetLoc] [Put ([c], Int), Get ([c], Int), Empty] '[] '[]
satisfyState = interpretM satisfyAlg

{--- LAMBDA PARSER ---}

{-
    Here we implement the parser for the polymorphic lambda calculus.
    This includes a Label effect that optionally tags sub-parsers with
    information for tracing. The information (n, e, v) represents:
        * n: The name of the parser.
        * e: ???
        * v: ???
-}

type Tag = (String, Bool)
type PSig = [Satisfy Char, GetLoc, Label Tag, Empty, Choose, Commit, CutCall]

trace :: Member (Tell [Trace]) sig => [Trace] -> Prog sig ()
trace = tell @[Trace]

name :: Members PSig sig => String -> Prog sig a -> Prog sig a
name s p = label (s, True) p

suppress :: Members PSig sig => Prog sig a -> Prog sig a
suppress p = label ("", False) p

{- What follows is a standard parser -}

keywords :: [String]
keywords = ["let", "in"]

notKeyword :: Members PSig sig => String -> Prog sig ()
notKeyword x = guard (not (x `elem` keywords))

whitespace :: Members PSig sig => Prog sig ()
whitespace = suppress $ void $ many (satisfy (==' '))

symbol :: Members PSig sig => Char -> Prog sig Char
symbol c = name s $ satisfy (==c) <* whitespace where
    s = "symbol " ++ show c

string :: Members PSig sig => String -> Prog sig String
string s = name t $ mapM (\c -> satisfy (==c)) s <* whitespace where
    t = "string \"" ++ s ++ "\""

ident :: Members PSig sig => Prog sig String
ident = name "identifier" $ do
    x <- suppress $ some (satisfy isAlphaNum)
    whitespace
    notKeyword x
    return x

parens :: Members PSig sig => Prog sig a -> Prog sig a
parens p = symbol '(' *> p <* symbol ')'

-- Left-factorising
boundT, halfT, tyT :: Members PSig sig => Prog sig (Ty String)
boundT = Bound <$> ident
halfT = parens tyT <|> boundT
tyT = do
    t <- halfT
    ts <- many (string "->" *> tyT)
    return (foldr1 Arr (t:ts))

type T = (String, Maybe (Ty String))

-- This runs a parser and then labels the result with positional information:
--   * The start position of the read data.
--   * The length of the read data.
track :: Members PSig sig => Prog sig (Term (Label Pos ': VAAL T)) -> Prog sig (Term (Label Pos ': VAAL T))
track p = do
    n1 <- getLoc
    t <- p
    n2 <- getLoc
    return (label (n1, n2 - n1) t)

-- A tracked versio of foldl
trackFoldlSome :: (Members PSig sig, Members '[Label Pos] sig')
    => Prog sig (Prog sig' a) -> (Prog sig' a -> Prog sig' a -> Prog sig' a) -> Prog sig (Prog sig' a)
trackFoldlSome p f = do
    n <- getLoc
    t:ts <- some (liftA2 (,) p getLoc)
    case ts of
        [] -> return (fst t)
        _ -> return $ foldl g (fst t) ts where
            g t1 (t2, n') = label (n, n' - n) (f t1 t2)

-- Parser for variables labelled with a type
typedP :: Members PSig sig => Prog sig T
typedP = parens p <|> p where
    p = do
        x <- ident
        --(string "::" *> tyT >>= \t -> return (x, Just t)) <|> return (x, Nothing)
        return (x, Nothing)

-- Core parser for the syntax
fullP, termP, absP, varP, letP :: Members PSig sig => Prog sig (Term (Label Pos ': VAAL T))
varP = name "var" $ var <$> typedP
absP = name "abs" $ do
    symbol '\\'
    commit
    x <- typedP
    symbol '.'
    t <- termP
    return (abs x t)
letP = name "let" $ do
    string "let"
    commit
    x <- typedP
    symbol '='
    m <- termP
    string "in"
    n <- termP
    return (lett x m n)
fullP = parens termP <|> track (absP <|> letP <|> varP)
termP = trackFoldlSome fullP app


{--- HANDLERS ---}

{-
    Here are the handlers for the parser.
    First we have the handler that elaborates parser labels into instructions
    for generating a trace. Then we have the handler that actually does the
    parsing.
-}

type Sig1 = [Label Tag, Empty, Choose, Commit, CutCall]
type Sig2 = [Empty, Choose, Commit, CutCall, Tell [Trace], Censor [Trace]]

-- This handler takes the labels and reinterprets them into other effects
-- that can generate a trace. There is no actual tracing done yet; rather,
-- the labels are transformed into programs that will do the trace once
-- reached.
-- The other operations are kept as is.
mtH :: Handler Sig1 Sig2 '[] '[]
mtH = interpretM f where
    f :: forall m . Monad m
      => (forall x . Effs Sig2 m x -> m x)
      -> (forall x . Effs Sig1 m x -> m x)
    f oalg op
        | Just (Scp (Label (n, e) k))    <- prj @(Label Tag) op = do
            let g = case e of
                    True  -> \ts -> [TEnter n ts]
                    False -> \_ -> []
            oalg $ inj (Scp (Censor g k))
        | Just (Alg Empty)          <- prj op = eval oalg $ do
            trace [TFailure]
            empty
        | Just (Scp (Choose mx my))   <- prj op = oalg $ inj (Scp (Choose mx my))
        | Just (Alg (Commit x))     <- prj op = eval oalg $ do
            trace [TCommit]
            commit
            return x
        | Just (Scp (CutCall mx))    <- prj op = do
            x <- mx
            eval oalg $ do
                cutCall (return x)
        | otherwise                           = undefined
    
-- This is the algebra that performs the backtracking. Most of the code that
-- supports this is in `Control.Effect.Cut`.
cutItemAlg :: Monad m
    => (forall x . oeff m x -> m x)
    -> (forall x . Effs [Empty, Choose, Commit, CutCall] (CutItemT m) x -> CutItemT m x)
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

-- A different handler for Censor that doesn't assume the applied function is
-- a homomorphism
censorsAlg
    :: forall w m. (Monad m, Monoid w)
    => (forall x . Effs [Put [w], Get [w]] m x -> m x)
    -> (forall x . Effs [Tell w, Censor w] m x -> m x)
censorsAlg oalg op
    | Just (Alg (Tell w k)) <- prj @(Tell w) op = eval oalg $ do
        xs <- get @[w]
        case xs of
            [] -> put @[w] [w]
            (y:ys) -> put @[w] (y `mappend` w : ys)
        return k
    | Just (Scp (Censor f k)) <- prj @(Censor w) op = do
        eval oalg $ do
            xs <- get @[w]
            put @[w] (mempty : xs)
        r <- k
        eval oalg $ do
            ys <- get @[w]
            case ys of
                (z:z':zs) -> put @[w] (z' `mappend` f z : zs)
                [z] -> put @[w] [f z]
                [] -> undefined
        return r
    | otherwise = undefined

-- The top-level parser functions
parse' :: String -> Prog PSig a -> Maybe ((String, Int), a)
parse' s = handle (hSatisfy |> labelIgnore |> cutItem) where
    hSatisfy = satisfyState ||> state (s, 0)

parse :: Prog PSig (Term (Label Pos ': VAAL a)) -> String -> Maybe (Int, Term (Label Pos ': VAAL a))
parse p s = do
    ((_, n), t) <- parse' s p
    return (n, t)

censors2 :: forall w . Monoid w => Handler [Tell w, Censor w] '[] '[Strict.StateT [w]] '[((,) w)]
censors2 = handler (fmap (\(x, y) -> (head y, x)) . flip Strict.runStateT []) (\f -> censorsAlg @w (stateAlg f))

pH :: String -> Prog PSig a -> ([Trace], Maybe ((String, Int), a))
pH s = handle (hSatisfy |> (mtH ||> (cutItem |> censors2))) where
    hSatisfy = satisfyState ||> state (s, 0)

parseH :: Prog PSig (Term (Label Pos ': VAAL a)) -> String -> ([Trace], Maybe (Int, Term (Label Pos ': VAAL a)))
parseH p s = let (tr, q) = pH s p in (tr, do { ((_, n), t) <- q; return (n, t) })

--parseT :: String -> Prog PSig a -> (String, Maybe (String, a))
--parseT s = handle ((satisfyState ||> state s) |> (mtH ||> (cutItem |> writer)))
