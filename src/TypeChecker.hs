{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeChecker where

import Control.Monad.Except
import Data.List

-- Symbols
type Symb = String

infixl 4 :@
infixr 3 :->
 
-- Terms
data Expr = Var Symb 
            | Expr :@ Expr
            | Lam Symb Type Expr
    deriving (Eq,Show)
 
-- Types
data Type = TVar Symb 
            | Type :-> Type
    deriving (Eq,Show)

-- Environment
newtype Env = Env [(Symb, Type)]

-- Inferring type predicating on specified variables' types (that must be stated by Cherch) 
inferType :: MonadError String m => Env -> Expr -> m Type
inferType (Env g) (Var x) = maybe (throwError $ show (Var x) ++ " has no type stated") (return . snd) (find ((== x) . fst) g)
inferType (Env g) (Lam x tx tm) = pp >>= (\v -> return $ tx :-> v) where pp = inferType (Env $ (x, tx):g ) tm
inferType e (tm1 :@ tm2) = do
    r <- inferType e tm1
    let i1 :-> j = r
    i2 <- inferType e tm2
    if i1 == i2
        then return j 
        else throwError $ show i1 ++ " differs from " ++ show i2

-- Checks if inferred type is the one that given term supposed to have
check :: Env -> Expr -> Type -> Bool 
check e tm tt = case inferType e tm of
    Right pp -> pp == tt
    Left _ -> False

