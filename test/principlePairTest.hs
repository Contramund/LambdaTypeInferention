import Test.HUnit
import System.Exit
import TypelessChecker

test1::Test
test1 = TestCase (do -- λx.λy.x
                    let Right pp = principlePair (Env []) (Lam "x" $ Lam "y" $ Var "x")
                    let ans = (Env [],TVar "A" :-> (TVar "C" :-> TVar "A")) 
                    assertEqual "" pp ans )

test2::Test
test2 = TestCase (do -- λx.x
                    let Right pp = principlePair (Env []) (Lam "x" $ Var "x")
                    let ans = (Env [],TVar "A" :-> TVar "A")
                    assertEqual "" pp ans )

test3::Test
test3 = TestCase (do -- λx.λy.y
                    let Right pp = principlePair (Env []) (Lam "x" $ Lam "y" $ Var "y")
                    let ans = (Env [],TVar "A" :-> (TVar "C" :-> TVar "C")) 
                    assertEqual "" pp ans )

test4::Test
test4 = TestCase (do -- λf.λg.λx.f(gx)
                    let Right pp = principlePair (Env []) (Lam "f" $ Lam "g" $ Lam "x" $ Var "f" :@ ( Var "g" :@ Var "x" ))
                    let ans = (Env [],(TVar "G" :-> TVar "F") :-> ((TVar "E" :-> TVar "G") :-> (TVar "E" :-> TVar "F")))
                    assertEqual "" pp ans )

test5::Test
test5 = TestCase (do -- λf.λg.λx.fx(gx)
                    let Right pp = principlePair (Env []) (Lam "f" $ Lam "g" $ Lam "x" $ Var "f" :@ Var "x" :@ ( Var "g" :@ Var "x" ))
                    let ans = (Env [],(TVar "E" :-> (TVar "G" :-> TVar "F")) :-> ((TVar "E" :-> TVar "G") :-> (TVar "E" :-> TVar "F")))
                    assertEqual "" pp ans )

test6::Test
test6 = TestCase (do -- λf.(λz.f(zz))(λz.f(zz))
                    let Left pp = principlePair (Env []) (Lam "f" $ (Lam "z" $ Var "f" :@ (Var "z" :@ Var "z")) :@ (Lam "z" $ Var "f" :@ (Var "z" :@ Var "z")))
                    let ans = "Can't unify (TVar \"D\") with (TVar \"D\" :-> TVar \"F\")!" 
                    assertEqual "" pp ans )

test7::Test
test7 = TestCase (do -- (λx.xx)(λx.xx)
                    let Left pp = principlePair (Env []) ((Lam "x" $ Var "x" :@ Var "x") :@ (Lam "x" $ Var "x" :@ Var "x"))
                    let ans = "Can't unify (TVar \"B\") with (TVar \"B\" :-> TVar \"C\")!"
                    assertEqual "" pp ans)

test8::Test
test8 = TestCase (do -- (λx.λy.xy)(λz.z)
                    let Left pp = principlePair (Env []) ((Lam "x" $ Lam "y" $ Var "x" :@ Var "y") :@ (Lam "z" $ Var "z"))
                    let ans = "Can't unify (TVar \"E\") with (TVar \"D\" :-> TVar \"E\")!"
                    assertEqual "" pp ans)

test9::Test
test9 = TestCase (do -- (λy.y)((λx.x)(λz.z))
                    let Left pp = principlePair (Env []) ((Lam "y" $ Var "y") :@ ((Lam "x" $ Var "x") :@ (Lam "z" $ Var "z")))
                    let ans = "Can't unify (TVar \"A\") with (TVar \"A\" :-> TVar \"A\")!"
                    assertEqual "" pp ans)

main :: IO ()
main = do
    cs@(Counts _ _ errs fails) <- runTestTT $ TestList
        [ TestLabel "cK: λ ⊢ x.λy.x" test1
        , TestLabel "cI: ⊢ λx.x" test2
        , TestLabel "cK_ast: ⊢ λx.λy.y" test3
        , TestLabel "cB: ⊢ λf.λg.λx.f(gx)" test4
        , TestLabel "cS: ⊢ λf.λg.λx.fx(gx)" test5
        , TestLabel "cY: ⊢ λf.(λz.f(zz))(λz.f(zz))" test6
        , TestLabel " ⊢ (λx.xx)(λx.xx)" test7
        , TestLabel " ⊢ (λx.λy.xy)(λz.z)" test8
        , TestLabel " ⊢ (λy.y)((λx.x)(λz.z))" test9 ]
    putStrLn (showCounts cs)
    if( errs > 0 || fails > 0 )
        then exitFailure
        else exitSuccess
