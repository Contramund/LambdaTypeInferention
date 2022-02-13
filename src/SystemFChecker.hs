{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TypeChecker where

import Control.Monad.Except
import Data.List

-- Symbols
type Symb = String

infixl 4 :@
infixr 3 :->
 
-- Types
data Type = TVar Symb 
            | Type :-> Type
            | V Symb Type
    deriving (Eq,Show)


-- Terms
data Expr = Var Symb 
            | Expr :@ Expr
            | Lam Symb Type Expr
            | LAM Symb Expr
            | Expr :@ Type
    deriving (Eq,Show)
 

-- Environment
newtype Env = Env [(Symb, Type)]

allPairs :: [Type] -> [Type] -> [(Type, Type)]
allPairs x:gx m = ( concatMap (\y->(x, y)) m) : (allPairs gx m)

subSTy :: => (Symb, Type) -> Type -> [Type]
subSTy a@[x, tb] tr     | tb == tr = [TVar x, tr] 
                        | otherwise = case tr of
                            e1 :-> e2 -> do 
                                let mas = allPairs (subSTy a e1) (subSTy a e2)
                                return $ concatMap (\(a,b) -> a :-> b ) mas
                            TVar s -> [TVar s]
                            V s t -> concatMap (\y -> V s y) $ subSTy a t

-- Inferring type predicating on specified variables' types (that must be stated by Cherch) 
inferType :: MonadError String m => Env -> Expr -> Type -> m [Type]
inferType (Env g) (Var x) t = maybe (throwError $ show (Var x) ++ " has no type stated") (return . (\x -> [snd x]) ) (find ((\y -> (TVar x == t) && ( y== x)) . fst) g)
inferType (Env g) (Lam x tx tm) t = do
                                        let res = inferType (Env $ (x, tx):g ) tm
                                        t1 :-> t2 <- t
                                        let ans = filter (== t2) res
                                        if tx == t1 && (not $ null $ ans )
                                            then return $ map (\a -> a >>= (\v -> tx :-> v)) ans
                                            else throwError $ "Not equal to given type"

inferType e (tm1 :@ tm2::Expr) t = do
    ans1 <- inferType e tm1
    ans2 <- inferType e tm2
    let pairs = allPairs ans1 ans2
    let ans = filter (\(r,i2) -> do
                                    i1 :-> j <- r
                                    return $ i1 == i2 && j == t) pairs
    return $ map (\(r,i2) -> do 
                                i1 :-> j <- r 
                                return j ) ans

inferType e (LAM x tm) t = if null $ filter (\i-> fst i == x) g 
                    then case t of
                        V x tm' -> if tm' == inferType e tm
                                        then return $ V x tm'
                                        else throwError $ "Not equal to given type"
                    else throwError $ "Wrong \"V\"-abstraction : Varaible \"" ++ x ++ "\" is already used in context."
inferType e (tm1 :@ tm2::Type) t = do 
    let res = map ( \y -> inferType e tm1 (V "?" y)) $ subSTy ("?", tm2) t
    return $ not $ null $ filter (\x -> case x of
                                            Left _ -> False)


-- Checks if inferred type is the one that given term supposed to have
check :: Env -> Expr -> Type -> Bool 
check e tm tt = case inferType e tm of
    Right pp -> pp == tt
    Left _ -> False

