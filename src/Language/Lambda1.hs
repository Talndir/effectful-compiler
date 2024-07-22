module Language.Lambda1 where

data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam a (Term a)
    deriving Functor

instance Show a => Show (Term a) where
    showsPrec p e = case e of
        Var x -> shows x
        App t1 t2 ->
            showParen (p > appPrec)
            ( showsPrec appPrec t1
            . showString " "
            . showsPrec (appPrec + 1) t2)
        Lam x t ->
            showParen (p > lamPrec)
            ( showString "λ "
            . shows x
            . showString " . "
            . showsPrec (lamPrec + 1) t)
        where
            appPrec = 10
            lamPrec = 5

data Ty
    = TVar String
    | TArr Ty Ty

instance Show Ty where
    showsPrec p t = case t of
        TVar x -> showString x
        TArr t1 t2 ->
            showParen (p > arrPrec)
            ( showsPrec arrPrec t1
            . showString " -> "
            . showsPrec (arrPrec + 1) t2)
        where
            arrPrec = 10
