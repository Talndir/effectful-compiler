{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Parsing.Parser4 where

import Prelude hiding (abs, log)
import Control.Applicative
import Control.Monad
import Data.Char (isAlphaNum)

import Control.Effect
import Control.Effect.Nondet
import Control.Effect.State
import Control.Effect.Cut
import Control.Effect.Writer

import Control.Family.Algebraic
import Control.Family.Scoped

import Language.Lambda2
import CutItem
import Effect.Label
import Trace

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

satisfyState :: Handler '[Satisfy c, GetLoc] [Put ([c], Int), Get ([c], Int), Empty] '[] '[]
satisfyState = interpretM satisfyAlg

type Tag = (String, Bool, Bool)
type PSig = [Satisfy Char, GetLoc, Label Tag, Empty, Choose, Commit, CutCall]

trace :: Member (Tell [Trace]) sig => [Trace] -> Prog sig ()
trace = tell @[Trace]

name :: Members PSig sig => String -> Prog sig a -> Prog sig a
name s p = label (s, True, True) p

name' :: Members PSig sig => String -> Prog sig a -> Prog sig a
name' s p = label (s, False, True) p

keywords :: [String]
keywords = ["let", "in"]

notKeyword :: Members PSig sig => String -> Prog sig ()
notKeyword x = guard (not (x `elem` keywords))

whitespace :: Members PSig sig => Prog sig ()
whitespace = void $ many (satisfy (==' '))

symbol :: Members PSig sig => Char -> Prog sig Char
symbol c = name' s $ satisfy (==c) <* whitespace where
    s = "symbol " ++ show c

string :: Members PSig sig => String -> Prog sig String
string s = name' t $ mapM (\c -> satisfy (==c)) s <* whitespace where
    t = "string \"" ++ s ++ "\""

ident :: Members PSig sig => Prog sig String
ident = name' "identifier" $ do
    x <- some (satisfy isAlphaNum)
    whitespace
    notKeyword x
    return x

parens :: Members PSig sig => Prog sig a -> Prog sig a
parens p = symbol '(' *> p <* symbol ')'

boundT, halfT, tyT :: Members PSig sig => Prog sig (Ty String)
boundT = Bound <$> ident
halfT = parens tyT <|> boundT
tyT = do
    t <- halfT
    ts <- many (string "->" *> tyT)
    return (foldr1 Arr (t:ts))

type T = (String, Maybe (Ty String))

track :: Members PSig sig => Prog sig (Term (Label Pos ': VAAL T)) -> Prog sig (Term (Label Pos ': VAAL T))
track p = do
    n1 <- getLoc
    t <- p
    n2 <- getLoc
    return (label (n1, n2 - n1) t)

trackFoldlSome :: (Members PSig sig, Members '[Label Pos] sig')
    => Prog sig (Prog sig' a) -> (Prog sig' a -> Prog sig' a -> Prog sig' a) -> Prog sig (Prog sig' a)
trackFoldlSome p f = do
    n <- getLoc
    t:ts <- some (liftA2 (,) p getLoc)
    case ts of
        [] -> return (fst t)
        _ -> return $ foldl g (fst t) ts where
            g t1 (t2, n') = label (n, n' - n) (f t1 t2)

fullP, termP, absP, varP, letP :: Members PSig sig => Prog sig (Term (Label Pos ': VAAL T))
typedP :: Members PSig sig => Prog sig T
typedP = parens p <|> p where
    p = do
        x <- ident
        (string "::" *> tyT >>= \t -> return (x, Just t)) <|> return (x, Nothing)

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

type Sig1 = [Label Tag, Empty, Choose, Commit, CutCall]
type Sig2 = [Empty, Choose, Commit, CutCall, Tell [Trace], Censor [Trace]]

mtH :: Handler Sig1 Sig2 '[] '[]
mtH = interpretM f where
    f :: forall m . Monad m
      => (forall x . Effs Sig2 m x -> m x)
      -> (forall x . Effs Sig1 m x -> m x)
    f oalg op
        | Just (Scp (Label (n, e, _) k))    <- prj @(Label Tag) op = do
            --eval oalg $ trace ("Trying " ++ n)
            --let g = case e of
            --        True -> map ("\t"++)
            --        False -> const []
            let g ts = [TEnter n ts]
            x <- oalg $ inj (Scp (Censor g k))
            --eval oalg $ trace ("\tSUCCESS")
            return x
        | Just (Alg Empty)          <- prj op = eval oalg $ do
            trace [TFailure]
            empty
        | Just (Scp (Choose mx my))   <- prj op = oalg $ inj (Scp (Choose mx my))
        | Just (Alg (Commit x))     <- prj op = eval oalg $ do
            trace []
            commit
            return x
        | Just (Scp (CutCall mx))    <- prj op = do
            x <- mx
            eval oalg $ do
                cutCall (return x)
        | otherwise                           = undefined
    

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

parse' :: String -> Prog PSig a -> Maybe ((String, Int), a)
parse' s = handle (hSatisfy |> labelIgnore |> cutItem) where
    hSatisfy = satisfyState ||> state (s, 0)

parse :: Prog PSig (Term (Label Pos ': VAAL a)) -> String -> Maybe (Int, Term (Label Pos ': VAAL a))
parse p s = do
    ((_, n), t) <- parse' s p
    return (n, t)

pH :: String -> Prog PSig a -> ([Trace], Maybe ((String, Int), a))
pH s = handle (hSatisfy |> (mtH ||> (cutItem |> censors @[Trace] id |> writer))) where
    hSatisfy = satisfyState ||> state (s, 0)

parseH :: Prog PSig (Term (Label Pos ': VAAL a)) -> String -> ([Trace], Maybe (Int, Term (Label Pos ': VAAL a)))
parseH p s = let (tr, q) = pH s p in (tr, do { ((_, n), t) <- q; return (n, t) })

--parseT :: String -> Prog PSig a -> (String, Maybe (String, a))
--parseT s = handle ((satisfyState ||> state s) |> (mtH ||> (cutItem |> writer)))
