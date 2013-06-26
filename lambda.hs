{-
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4
-}

-- for the union function and other list utilities
import Data.List

-- type alias for variable names
type Varname = String

{-
 - We define lambda expressions inductively as either 
 - * an application of two expression,
 - * an abstraction with a variable and an expression,
 - * a De Brujn-indexed bound variable,
 - * or a Free variable
 -}
data Expr = Expr :$: Expr | Abs Varname Expr | Var Integer | Free Varname


-- The freeVars function generates a list of free variables in an expression.
-- We need this list to rename bound variables for printing.
freeVars    (Free x) = [x]
freeVars     (Var i) = []
freeVars   (Abs v e) = freeVars e
freeVars (x0 :$: x1) = freeVars x0 `union` freeVars x1

-- This function pretty-prints a lambda expression.
lambdaPrint exp = lambdaPrint' exp []
  where lambdaPrint' (Free x) _ = x
        -- the ctxt variable is a list of used variable names
        lambdaPrint' (Var 0) ctxt = head ctxt
        lambdaPrint' (Var n) ctxt = lambdaPrint' (Var (n-1)) (tail ctxt)
        lambdaPrint' (Abs v x) ctxt
          | v `elem` freeVars x || v `elem` ctxt = lambdaPrint' (Abs (v++"'") x) ctxt   -- here we rename a variable because it is in the context or in the free vars...
          | otherwise = "(λ" ++ v ++ "." ++ lambdaPrint' x (v:ctxt) ++ ")"              -- ...and here we use an available variable name we found and put it into the context
        lambdaPrint' (x0 :$: x1) ctxt = "(" ++ lambdaPrint' x0 ctxt ++ " " ++ lambdaPrint' x1 ctxt ++ ")"

-- Show declaration for automatic pretty-printing
instance Show Expr where
  show = lambdaPrint

-- substitution function. Here we make use of the De Brujn indices.
substitute s i (x0 :$: x1) = substitute s i x0 :$: substitute s i x1
substitute s i (Abs v x) = Abs v (substitute s (i+1) x)
substitute s i (Var j)
  | i == j = s
  | otherwise = Var j
substitute s i x = x

-- This function performs exactly one betaReduction if possible, or none if none is possible.
-- It returns a Just Expr if it performed a reduction, and Nothing if it didn't.

betaReduction (Abs v x :$: r) = Just (substitute r 0 x) -- Application onto an abstraction can always be reduced and consumes the abstraction
betaReduction (Abs v x) =                               -- Abstraction in general is reduced by reducing the abstraction body. Note how Nothing is returned if the reduction of the body returns Nothing.
  case betaReduction x of
    Just x' -> Just (Abs v x')
    Nothing -> Nothing
betaReduction (x0 :$: x1) =                             -- Application in general first reduces the left side, and if that is irreducible, the right side.
  case betaReduction x0 of
    Just x0' -> Just (x0' :$: x1)
    Nothing -> case betaReduction x1 of
                 Just x1' -> Just (x0 :$: x1')
                 Nothing -> Nothing
betaReduction _ = Nothing                               -- Variables do not reduce

-- Normalization: Reduce until Nothing is returned
betaNormalize x =
  case betaReduction x of
    Just x0 -> betaNormalize x0
    Nothing -> x

-- Combinators
tSelf = Abs "x" (Var 0 :$: Var 0)
tOmega = tSelf :$: tSelf                -- the infamous omega combinator. I tried to reduce it. I'm still working on it.
tI = Abs "x" (Var 0)
tK = Abs "x" (Abs "y" (Var 1))
tS = Abs "x" (Abs "y" (Abs "z" (Var 2 :$: Var 0) :$: (Var 1 :$: Var 0)))

-- Terms                                                                                    -- Results

t1  = Abs "x" (Abs "y" (Var 1 :$: Var 0)) :$: Free "y"                                      -- (λy'.(y y'))
t2  = Abs "x" (Abs "x" (Var 0)) :$: Free "y"                                                -- (λx.x)
t3  = (tK :$: Free "c") :$: tOmega                                                          -- c
t4  = (Abs "x" ((((Free "f") :$: (Var 0)) :$: (Var 0))) :$: (Free "5"))                     -- ((f 5) 5)
t5  = (Abs "x" (Var 0)) :$: (Abs "x" (Var 0))                                               -- (λx.x)
t6  = (Free "x") :$: (Abs "y" (Var 0))                                                      -- (x (λy.y))
t7  = tSelf :$: Abs "x" ((Free "f") :$: (Var 0))                                            -- (f (λx.(f x)))
t8  = ((tS :$: tK) :$: (Free "x")) :$: (Free "y")                                           -- (λy.x)
t9  = ((tS :$: tK) :$: tK) :$: (Free "x")                                                   -- (λy.(λx.(λy'.x)))
t10 = (Abs "x" (Abs "y" ((Var 1) :$: tI))) :$: (Abs "y" ((Free "x") :$: (Var 0)))           -- (λy.(x (λx.x)))
t11 = (Abs "x" ((Abs "y" ((Var 1) :$: (Var 0)) :$: (Free "c")))) :$: (tI :$: (Free "d"))    -- (d c)
