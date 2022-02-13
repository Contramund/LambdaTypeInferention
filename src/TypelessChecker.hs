
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module TypelessChecker where

import Data.List
import Data.Maybe
import Data.Char
import Data.Bifunctor
import Control.Monad.Except

infixl 4 :@
infixr 3 :->

type Symb = String 

-- Type
data Type = TVar Symb 
            | Type :-> Type
    deriving (Eq,Show)

-- Term
data Expr = Var Symb 
            | Expr :@ Expr
            | Lam Symb Expr
            | LamT Symb Type Expr
    deriving (Eq,Show)

-- Context
newtype Env = Env [(Symb,Type)]
    deriving (Eq,Show)

-- Substitution
newtype SubsTy = SubsTy [(Symb, Type)]
    deriving (Eq,Show)

-- Function to get free variables of expression
freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (e1 :@ e2) = nub $ freeVars e1 ++ freeVars e2
freeVars (Lam x e1) = delete x (freeVars e1)
freeVars (LamT x t e1) = delete x (freeVars e1)

-- Function to get free variables of Type
freeTVars :: Type -> [Symb]
freeTVars (TVar x) = [x]
freeTVars (t1 :-> t2) = freeTVars t1 ++ freeTVars t2

-- Function to get free type variables of context
freeTVarsEnv :: Env -> [Symb]
freeTVarsEnv (Env e) = concatMap (freeTVars . snd) e

-- Function to substitute type instead of type's variables in type
appSubsTy :: SubsTy -> Type -> Type
appSubsTy (SubsTy sbs) (TVar x) =  maybe (TVar x) snd (find ((== x) . fst) sbs)
appSubsTy sbs (t1 :-> t2) = appSubsTy sbs t1 :-> appSubsTy sbs t2

-- Function to substitute type instead of type's variables in context
appSubsEnv :: SubsTy -> Env -> Env
appSubsEnv sbs (Env e) = Env $ map (second (appSubsTy sbs)) e

-- Function to get the conposition of two substitutions
composeSubsTy :: SubsTy -> SubsTy -> SubsTy
composeSubsTy s@(SubsTy s2) (SubsTy s1) = SubsTy $
    filter (\x -> fst x `notElem` map fst s1) s2 ++ map (second (appSubsTy s)) s1

-- Give SubsTy a semigroup structure
instance Semigroup SubsTy where
    s1 <> s2 = composeSubsTy s1 s2

-- Give SubsTy a monoid structure
instance Monoid SubsTy where
    mempty = SubsTy []

-- Function to substitute environment variable instead of symbol (if fails returns error message)
appEnv :: MonadError String m => Env -> Symb -> m Type
appEnv (Env xs) v = maybe (throwError $ "There is no variable " ++ show v ++ " in the enviroment.") (return . snd) (find ((== v) . fst) xs)

-- Function to get the most common unificator of two types (if fails returns error message)
unify :: MonadError String m => Type -> Type -> m SubsTy
unify (TVar x) (TVar y) | x == y = return $ SubsTy []
unify (TVar x) t        | x `elem` freeTVars t = throwError $ "Can't unify (TVar " ++ show x ++ ") with (" ++ show t ++ ")!"
                        | otherwise = return $ SubsTy [(x, t)]
unify t@(_ :-> _) x@(TVar _) = unify x t -- swap trick
unify (s1 :-> s2) (t1 :-> t2) = do
    u <- unify s2 t2
    u' <- unify (appSubsTy u s1) (appSubsTy u t1)
    return $ u' <> u

-- Function to ger the next by code char
nextChar :: Char -> Char
nextChar c = chr (((1 + ord c - ord 'A') `mod` 26) + ord 'A')

-- Function to get new name for symbol
newSymb :: Symb -> [Symb] -> Symb
newSymb s@(s0:xs) as    | any (s ==) as && s0 /= 'Z' = newSymb ((nextChar s0):xs) as 
                        | any (s ==) as = newSymb ('A':s) as
                        | otherwise = s 

-- Function to get the system of the conditions on types with specified context
equations :: MonadError String m => Env -> Expr -> Type -> m [(Type,Type)]
equations g (Var x) s = do
    gx <- appEnv g x
    return [(s, gx)] -- inverse to right substitution later
equations (Env g) (e1 :@ e2) s =
    let a = newSymb "A" $ (sort $ freeTVars s ++ concatMap (freeTVars . snd) g) in do
        e1 <- equations (Env g) e1 (TVar a :-> s)
        e2 <- equations (Env $ ( "" , s) : g) e2 (TVar a) -- pass an empty symb to remember that `s` symbols are used 
        return $ nub $ e1 ++ e2
equations (Env g) (Lam x e) s = 
    let a = newSymb "A" $ (sort $ freeTVars s ++ concatMap (freeTVars . snd) g) 
        b = newSymb "A" $ (sort $ [a] ++ freeTVars s ++ concatMap (freeTVars . snd) g) in 
    if not $ null $ filter (\i-> fst i == x) g
        then throwError $ "Second appearence of " ++ x ++ "as an dependent variable!"
        else do
            e1 <- equations (Env $ ("", s) : (x, TVar a) : g) e (TVar b)
            return $ (TVar a :-> TVar b, s) : e1 
equations (Env g) (LamT x t e) s =
    let a = newSymb "A" $ (sort $ freeTVars s ++ concatMap (freeTVars . snd) g) 
        b = newSymb "A" $ (sort $ [a] ++ freeTVars s ++ concatMap (freeTVars . snd) g) in
    if not $ null $ filter (\i-> fst i == x) g
        then throwError $ "Second appearence of " ++ x ++ "as an dependent variable!"
        else do
            e1 <- equations (Env $ ("", s) : (x, t) : g) e (TVar a)
            return $ (t :-> TVar a, s) : e1 

-- Fold function on pair that concatinates corresponding elements with :-> separated
foldType :: [(Type, Type)] -> (Type, Type)
foldType t = (foldl1 (:->) $ map fst t, foldl1 (:->) $ map snd t)

-- Function to get new Type's names for all of the [2-nd arg] symbols differs from the [1-st arg] type names  
initEnv :: [Symb] -> [Symb] -> [(Symb, Type)]
initEnv _ [] = []
initEnv r (x : xs) = let n = newSymb "A" r in (x, TVar n) : initEnv (n:r) xs

principlePair :: MonadError String m => Env -> Expr -> m (Env,Type)
principlePair (Env g) x = do
    let gi = map fst g
    let g0 = initEnv (concatMap (freeTVars . snd) g) (filter (\x-> x `notElem` gi) $ freeVars x)
    (t1, t2) <- foldType <$> equations (Env $ g ++ g0) x (TVar "RES'")
    sbs <- unify t1 t2
    return (appSubsEnv sbs (Env $ g ++ g0), appSubsTy sbs (TVar "RES'"))

-- Function to get substitution if [1-nd arg] can be obtained from [1-st arg] by some replacements of variables to types
isSubtypeOf :: MonadError String m => Type -> Type -> m SubsTy
isSubtypeOf t (TVar x) = return $ SubsTy [(x++"!", t)]
isSubtypeOf x@(TVar _) t@(_ :-> _) = throwError $ "Cannot be a subtype in cause of " ++ show x ++ " must be equal to " ++ show t
isSubtypeOf (s1 :-> s2) (t1 :-> t2) = do
    u  <- isSubtypeOf s2 t2
    u' <- isSubtypeOf s1 (appSubsTy u t1)
    return $ u' <> u

-- Function to check if expression has specified type
check :: Env -> Expr -> Type -> Bool
check e x t = case principlePair e x of
    Left _ -> False
    Right pp -> case (unify (snd pp) t) of
                    Left _ -> False
                    Right _ -> True

-- let Right pp = principlePair (Env [("y",TVar "GG" :-> (TVar "AA" :-> TVar "BB")),("z", TVar "GG")]) (LamT "x" ((TVar "AA" :-> TVar "BB") :-> TVar "BB") $ Var "x" :@ Var "y" :@ Var "z") in pp
-- --> crashes
-- let Right pp = principlePair (Env [("y",TVar "GG" :-> (TVar "AA" :-> TVar "BB")),("z", TVar "GG")]) (LamT "x" ((TVar "AA" :-> TVar "BB") :-> TVar "BB") $ Var "x" :@ (Var "y" :@ Var "z")) in pp
-- --> (Env [("y",TVar "GG" :-> (TVar "AA" :-> TVar "BB")),("z",TVar "GG")],((TVar "AA" :-> TVar "BB") :-> TVar "BB") :-> TVar "BB")
-- let Right pp = principlePair (Env [("y", TVar "AA" :-> TVar "BB")]) (LamT "x" (TVar "G") $ Var "x" :@ Var "y") in pp
-- --> (Env [("y",TVar "AA" :-> TVar "BB")],((TVar "AA" :-> TVar "BB") :-> TVar "A") :-> TVar "A")
-- -------> should it replace TVar "G" with (TVar "AA" :-> TVar "BB") :-> TVar "A" with aim to infer type ???
-- let Right pp = principlePair (Env [("y", TVar "AA" :-> TVar "BB")]) (LamT "x" (TVar "G" :-> TVar "G") $ Var "x" :@ Var "y") in pp
-- --> (Env [("y",TVar "AA" :-> TVar "BB")],((TVar "AA" :-> TVar "BB") :-> (TVar "AA" :-> TVar "BB")) :-> (TVar "AA" :-> TVar "BB"))
-- -------> should it replace TVar "G" with (TVar "AA" :-> TVar "BB") with aim to infer type ???
--
--
