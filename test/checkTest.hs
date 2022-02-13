import Test.HUnit
import System.Exit
import TypeChecker

-- Simple tests

test1::Test
test1 = TestCase (do -- Ø ⊢ λx::A.λy::B.x
                    let env = Env []
                    let term = Lam "x" (TVar "A") $ Lam "y" (TVar "B") $ Var "x"
                    let ans = TVar "A" :-> (TVar "B" :-> TVar "A") 
                    assertEqual "" True $ check env term ans )

test2::Test
test2 = TestCase (do -- y::G->(A->B), z::G ⊢ λx::(A->B)->B.x(yz)
                    let env = Env [  ( "y", TVar "G" :-> (TVar "A" :-> TVar "B"))
                                  ,  ( "z", TVar "G") ]
                    let term = Lam "x" ((TVar "A" :-> TVar "B") :-> TVar "B") $ Var "x" :@ (Var "y" :@ Var "z")
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "B") :-> TVar "B"
                    assertEqual "" True $ check env term ans )
                    
test3::Test
test3 = TestCase (do -- Ø ⊢ λf::A->B.λg::C->A.λx::C.f(gx)
                    let env = Env [ ]
                    let term = Lam "f" (TVar "A" :-> TVar "B") $ Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let ans = (TVar "A" :-> TVar "B") :-> ((TVar "C" :-> TVar "A") :-> (TVar "C" :-> TVar "B"))
                    assertEqual "" True $ check env term ans )
                    
test4::Test
test4 = TestCase (do -- Ø ⊢ λg::C->A.λx::C.f(gx)
                    let env = Env [ ]
                    let term = Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let ans = TVar "F"
                    assertEqual "" False $ check env term ans )
                    
test5::Test
test5 = TestCase (do -- f::A->(B->X) ⊢ λg::C->A.λx::C.f(gx)
                    let env = Env [("f",TVar "A" :-> (TVar "B" :-> TVar "X")) ]
                    let term = Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let ans = (TVar "C" :-> TVar "A") :-> (TVar "C" :-> (TVar "B" :-> TVar "X"))
                    assertEqual "" True $ check env term ans )
                    
test6::Test
test6 = TestCase (do -- f::X->(B->X) ⊢ λg::C->A.λx::C.f(gx)
                    let env = Env [("f",TVar "X" :-> (TVar "B" :-> TVar "X")) ]
                    let term = Lam "g" (TVar "C" :-> TVar "A") $ Lam "x" (TVar "C") $ Var "f" :@ ( Var "g" :@ Var "x" )
                    let ans = TVar "Err"
                    assertEqual "" False $ check env term ans )
                    
-- Tests with terms from previous tasks
                   
test7::Test
test7 = TestCase (do -- Ø ⊢ λf::A->A->G.λg::A.λx::B.(fg)g
                    let env = Env [ ]
                    let term = Lam "f" (TVar "A" :-> TVar "A" :-> TVar "G") $ Lam "g" (TVar "A") $ Lam "x" (TVar "B") $ (Var "f" :@  Var "g" ) :@ Var "g" 
                    let ans = (TVar "A" :-> TVar "A" :-> TVar "G") :-> TVar "A" :-> TVar "B" :-> TVar "G"
                    assertEqual "" True $ check env term ans )
                    
test8::Test
test8 = TestCase (do -- Ø ⊢ λf::(A->G)->A.λg::A->G.λx::B.y(xy)
                    let env = Env [ ]
                    let term = Lam "f" ((TVar "A" :-> TVar "G" ) :-> TVar "A") $ Lam "g" (TVar "A" :-> TVar "G") $ Lam "x" (TVar "B") $ Var "g" :@  ( Var "f"  :@ Var "g") 
                    let ans = ((TVar "A" :-> TVar "G") :-> TVar "A") :-> (TVar "A" :-> TVar "G") :-> TVar "B" :-> TVar "G"
                    assertEqual "" True $ check env term ans )
                    
test9::Test
test9 = TestCase (do -- Ø ⊢ λf::(A->B)->A.λg::A->A->B.f(λx::A.gx(f(gx))
                    let env = Env [ ]
                    let term = Lam "f" ((TVar "A" :-> TVar "B" ) :-> TVar "A") $ Lam "g" (TVar "A" :-> TVar "A" :-> TVar "B") $ Var "f" :@ (Lam "x" (TVar "A") $ Var "g" :@ Var "x" :@ (Var "f" :@ (Var "g" :@ Var "x")))
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "A") :-> (TVar "A" :-> TVar "A" :-> TVar "B") :-> TVar "A"
                    assertEqual "" True $ check env term ans )
                    
test10::Test
test10 = TestCase (do -- Ø ⊢ λf::(A->B)->A.λg::A->A->B.g(λx::A.gSS, where S = f(λx::A.gx(f(gx)))
                    let env = Env [ ]
                    let subterm = Var "f" :@ (Lam "x" (TVar "A") $ Var "g" :@ Var  "x" :@ (Var "f" :@ (Var "g" :@ Var "x")))
                    let term = Lam "f" ((TVar "A" :-> TVar "B" ) :-> TVar "A") $ Lam "g" (TVar "A" :-> TVar "A" :-> TVar "B") $ Var "g" :@ subterm :@ subterm
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "A") :-> (TVar "A" :-> TVar "A" :-> TVar "B") :-> TVar "B"
                    assertEqual "" True $ check env term ans )
                    
test11::Test
test11 = TestCase (do -- x::A->B->G, y:A->B, z::A ⊢ xz(yz)
                    let env = Env [  ( "x", TVar "A" :-> TVar "B" :-> TVar "G")
                                  ,  ( "y", TVar "A" :-> TVar "B")
                                  ,  ( "z", TVar "A") ]
                    let term = Var "x" :@ Var "z" :@ ( Var "y" :@ Var "z" )
                    let ans = TVar "G" 
                    assertEqual "" True $ check env term ans )
                    
test12::Test
test12 = TestCase (do -- y::G->A->B, z::G ⊢ λx::(A->B)->B.x(yz)
                    let env = Env [  ( "y", TVar "G" :-> TVar "A" :-> TVar "B")
                                  ,  ( "z", TVar "G") ]
                    let term = Lam "x" ((TVar "A" :-> TVar "B") :-> TVar "B") $ Var "x" :@ (Var "y" :@ Var "z")
                    let ans = ((TVar "A" :-> TVar "B") :-> TVar "B") :-> TVar "B" 
                    assertEqual "" True $ check env term ans )
                    
test13::Test
test13 = TestCase (do -- x::A->A->B ⊢ λy::A.λz::(B->G).z(xyy)
                    let env = Env [  ( "x", TVar "A" :-> TVar "A" :-> TVar "B") ]
                    let term = Lam "y" (TVar "A") $ Lam "z" (TVar "B" :-> TVar "G") $ Var "z" :@ ( Var "x" :@ Var "y" :@ Var "y")
                    let ans = TVar "A" :-> (TVar "B" :-> TVar "G") :-> TVar "G"
                    assertEqual "" True $ check env term ans )
                    
test14::Test
test14 = TestCase (do -- y::B->A->G, z::A ⊢ λx::A->B.y(xz)z
                    let env = Env [  ( "y", TVar "B" :-> TVar "A" :-> TVar "G") 
                                  ,  ( "z", TVar "A") ]
                    let term = Lam "x" (TVar "A" :-> TVar "B") $ Var "y" :@ (Var "x" :@ Var "z") :@ Var "z"
                    let ans = (TVar "A" :-> TVar "B") :-> TVar "G"
                    assertEqual "" True $ check env term ans )

main :: IO ()
main = do
    cs@(Counts _ _ errs fails) <- runTestTT $ TestList
        [ TestLabel " cK: Ø ⊢ λx::A.λy::B.x" test1
        , TestLabel " Ø ⊢ λf::A->B.λg::C->A.λx::C.f(gx)" test3
        , TestLabel " Ø ⊢ λg::C->A.λx::C.f(gx)" test4
        , TestLabel " f::A->(B->X) ⊢ λg::C->A.λx::C.f(gx)" test5
        , TestLabel " f::X->(B->X) ⊢ λg::C->A.λx::C.f(gx)" test6
        , TestLabel " Ø ⊢ f::A->A->G).λg::A.λx::B.(fg)g" test7
        , TestLabel " Ø ⊢ λf::(A->G)->A.λg::A->G.λx::B.y(xy)" test8
        , TestLabel " Ø ⊢ λf::(A->B)->A.λg::A->A->B.f(λx::A.gx(f(gx))" test9
        , TestLabel " Ø ⊢ λf::(A->B)->A.λg::A->A->B.g(λx::A.gSS, where S = f(λx::A.gx(f(gx)))" test10
        , TestLabel " x::A->B->G, y:A->B, z::A ⊢ xz(yz)" test11
        , TestLabel " y::G->A->B, z::G ⊢ λx::(A->B)->B.x(yz)" test12
        , TestLabel " x::A->A->B ⊢ λy::A.λz::(B->G).z(xyy)" test13
        , TestLabel " y::B->A->G, z::A ⊢ λx::A->B.y(xz)z)" test14
        , TestLabel " ⊢ λv.λw.z(λz.uvvw)" test2]
    putStrLn (showCounts cs)
    if( errs > 0 || fails > 0 )
        then exitFailure
        else exitSuccess
