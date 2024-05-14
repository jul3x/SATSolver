module Main where

import System.IO
import System.Random
import Test.QuickCheck
import Data.List
import Data.Ord
import Formula
import Parser hiding (check)
import Utils



-- finds all variables occurring in the formula (sorted, without duplicates)
variables :: Formula -> [VarName]
variables = rmdups . go where
  go T = []
  go F = []
  go (Var x) = [x]
  go (Not phi) = go phi
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = go phi ++ go psi
  go (Implies phi psi) = go phi ++ go psi
  go (Iff phi psi) = go phi ++ go psi

-- truth valuations
type Valuation = VarName -> Bool

-- the evaluation function
eval :: Formula -> Valuation -> Bool
eval T _ = True
eval F _ = False
eval (Var x) rho = rho x
eval (Not phi) rho = not $ eval phi rho
eval (And phi psi) rho = (eval phi rho) && (eval psi rho)
eval (Or phi psi) rho = (eval phi rho) || (eval psi rho)
eval (Implies phi psi) rho = not (eval phi rho) || (eval psi rho)
eval (Iff phi psi) rho = eval phi rho == eval psi rho


-- formula simplification
simplify :: Formula -> Formula
simplify T = T
simplify F = F
simplify (Var p) = Var p

simplify (Not T) = F
simplify (Not F) = T
simplify (Not (Not phi)) = simplify phi
simplify (Not phi) = Not (simplify phi)

simplify (And T phi) = simplify phi
simplify (And phi T) = simplify phi
simplify (And F _) = F
simplify (And _ F) = F
simplify (And phi psi) = And (simplify phi) (simplify psi)

simplify (Or T _) = T
simplify (Or _ T) = T
simplify (Or F phi) = simplify phi
simplify (Or phi F) = simplify phi
simplify (Or phi psi) = Or (simplify phi) (simplify psi)

simplify (Implies T phi) = simplify phi
simplify (Implies _ T) = T
simplify (Implies F _) = T
simplify (Implies phi F) = simplify (Not phi)
simplify (Implies phi psi) = Implies (simplify phi) (simplify psi)

simplify (Iff T phi) = simplify phi
simplify (Iff phi T) = simplify phi
simplify (Iff F phi) = simplify (Not phi)
simplify (Iff phi F) = simplify (Not phi)
simplify (Iff phi psi) = Iff (simplify phi) (simplify psi)

-- keep simplifying until no more simplifications are possible
deep_simplify :: Formula -> Formula
deep_simplify phi = go where
  psi = simplify phi
  go | phi == psi = phi
     | otherwise = deep_simplify psi

-- compute the NNF (negation normal form)
nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Not T) = F
nnf (Not F) = T
nnf (Var p) = Var p
nnf (Not (Var p)) = Not $ Var p
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = nnf (Or (Not phi) psi)
nnf (Iff phi psi) = nnf (And (Implies phi psi) (Implies psi phi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = nnf (Or (Not phi) (Not psi))
nnf (Not (Or phi psi)) = nnf (And (Not phi) (Not psi))
nnf (Not (Implies phi psi)) = nnf (And phi (Not psi))
nnf (Not (Iff phi psi)) = nnf (Or (And phi (Not psi)) (And (Not phi) psi))

-- data structure used in the SAT solver
data Literal = Pos VarName | Neg VarName deriving (Eq, Show, Ord)

-- compute the opposite literal
opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type SatSolver = Formula -> Bool

cnf :: Formula -> [[Literal]]
cnf phi = go $ nnf phi where
  go T = []
  go F = [[]]
  go (Var x) = [[Pos x]]
  go (Not (Var x)) = [[Neg x]]
  go (And phi psi) = go phi ++ go psi
  go (Or phi psi) = distribute (go phi) (go psi)

-- TODO
-- transform a formula to equi-satisfiable cnf (linear complexity)
-- there is no assumption on the input formula
-- Hints:
-- - Create a fresh variable x_phi for every subformula phi.
-- - For a subformula of the form phi = phi1 op phi2, use cnf :: Formula -> [[Literal]] above to produce the cnf psi_phi of x_phi <--> x_phi1 op x_phi2
-- - Concatenate all the cnfs psi_phi for every subformula phi.
-- - See slide #5 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
ecnf :: Formula -> [[Literal]]
ecnf phi = result ++ [[Pos ("v" ++ show var)]] where
  (result, var) = ecnf' phi 0

ecnf' (Or phi psi) y = (left_res ++ right_res ++
                      cnf (Iff (Var ("v" ++ show (right_var + 1))) (Or (Var ("v" ++ show (left_var))) (Var ("v" ++ show (right_var))))), 
                      right_var + 1)
  where (left_res, left_var) = ecnf' phi y
        (right_res, right_var) = ecnf' psi left_var
ecnf' (And phi psi) y = (left_res ++ right_res ++
                      cnf (Iff (Var ("v" ++ show (right_var + 1))) (And (Var ("v" ++ show (left_var))) (Var ("v" ++ show (right_var))))), 
                      right_var + 1)
  where (left_res, left_var) = ecnf' phi y
        (right_res, right_var) = ecnf' psi left_var
ecnf' (Iff phi psi) y = (left_res ++ right_res ++
                      cnf (Iff (Var ("v" ++ show (right_var + 1))) (Iff (Var ("v" ++ show (left_var))) (Var ("v" ++ show (right_var))))), 
                      right_var + 1)
  where (left_res, left_var) = ecnf' phi y
        (right_res, right_var) = ecnf' psi left_var
ecnf' (Implies phi psi) y = (left_res ++ right_res ++
                          cnf (Iff (Var ("v" ++ show (right_var + 1))) (Implies (Var ("v" ++ show (left_var))) (Var ("v" ++ show (right_var))))), 
                          right_var + 1)
  where (left_res, left_var) = ecnf' phi y
        (right_res, right_var) = ecnf' psi left_var
ecnf' (Not phi) y = (left_res ++
                          cnf (Iff (Var ("v" ++ show (left_var + 1))) (Not (Var ("v" ++ show (left_var))) )), left_var+1) 
  where (left_res, left_var) = ecnf' phi y
ecnf' x y = (cnf (Iff (Var ("v" ++ show (y+1))) x), y+1)


-- convert a CNF in the list of clauses form to a formula
-- entirely analogous to "dnf2formula" from Lab01
cnf2formula :: [[Literal]] -> Formula
cnf2formula [] = T
cnf2formula lss = foldr1 And (map go lss) where
  go [] = F
  go ls = foldr1 Or (map go2 ls)
  go2 (Pos x) = Var x
  go2 (Neg x) = Not (Var x)

-- find all positive occurrences of a variable name
positive_literals :: [Literal] -> [VarName]
positive_literals ls = rmdups [p | Pos p <- ls]

-- find all negative occurrences of a variable name
negative_literals :: [Literal] -> [VarName]
negative_literals ls = rmdups [p | Neg p <- ls]

-- find all occurrences of a variable name
literals :: [Literal] -> [VarName]
literals ls = rmdups $ positive_literals ls ++ negative_literals ls

positive_negative [] = ([],[])
positive_negative ((Pos l):ls) = (l : positives, negatives)
  where (positives, negatives) = positive_negative ls
positive_negative ((Neg l):ls) = (positives, l : negatives)
  where (positives, negatives) = positive_negative ls

compareList :: (Eq a) => [a] -> [a] -> Bool
compareList a = null . intersect a

remove_tautologies :: [[Literal]] -> [[Literal]]
remove_tautologies lss = filter (\x -> compareList (negative_literals x) (positive_literals x)) lss

one_literal :: [[Literal]] -> [[Literal]]
one_literal lss = one_literal' lss []

removeL l xs = filter (\y -> not (l `elem` y)) xs

removeOpposite l xs = map (\z -> filter (/= opposite l) z) xs

one_literal' [] done = done
one_literal' ([x]:xs) done = one_literal' (removeOpposite x (removeL x xs)) (removeOpposite x (removeL x done))
one_literal' (x:xs) done = one_literal' xs (x:done)

----------------------------------------------

get_all_positive_literals lls = rmdups (get_all_positive_literals' lls)
get_all_positive_literals' [] = []
get_all_positive_literals' (x:xs) = positive_literals x ++ get_all_positive_literals' xs

get_all_negative_literals lls = rmdups (get_all_negative_literals' lls)
get_all_negative_literals' [] = []
get_all_negative_literals' (x:xs) = negative_literals x ++ get_all_negative_literals' xs

get_all_pure_literals lls = (neg \\ pos) ++ (pos \\ neg)
  where neg = get_all_negative_literals lls
        pos = get_all_positive_literals lls

affirmative_negative :: [[Literal]] -> [[Literal]]
affirmative_negative lss = affirmative_negative' lss (get_all_pure_literals lss)

affirmative_negative' lss [] = lss
affirmative_negative' lss (l:ls) = affirmative_negative' (filter (\clause -> not ((Neg l) `elem` clause || (Pos l) `elem` clause)) lss) ls

------------------
literals_in_clause ls = [p | Pos p <- ls, Neg p <- ls]

literal_to_pick lss = head . maximumBy (comparing length) . group . sort $ concat (map literals_in_clause lss)


-- the main DP satisfiability loop
-- this implements #15 of https://github.com/lclem/logic_course/blob/master/docs/slides/03-resolution.pdf
loop_DPLL :: [[Literal]] -> Bool
loop_DPLL [] = True -- if the CNF is empty, then it is satisfiable
loop_DPLL lss | elem [] lss = False -- if there is an empty clause, then the CNF is not satisfiable
loop_DPLL lss =
  -- apply one round of simplification by removing tautologies, applying the one-literal rule, and the affirmative_negative rule
  let lss' = rmdups . affirmative_negative . one_literal . remove_tautologies $ lss
      literal = literal_to_pick lss in
    if lss == lss'
      -- if the CNF didn't change, then do a resolution step (expensive)
      then 
        (loop_DPLL ([Neg literal]:lss)) || (loop_DPLL ([Pos literal]:lss))
      -- if the CNF didn chang, then do another round of simplifications recursively
      else loop_DPLL lss'

-- the DP SAT solver
sat_DPLL :: SatSolver
sat_DPLL = loop_DPLL . map rmdups . ecnf . deep_simplify

-- TODO
sat_solver :: Formula -> Bool
sat_solver phi = sat_DPLL phi



main :: IO Int
main = do
    eof <- hIsEOF stdin
    if eof
        then return 0
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let sat = sat_solver phi -- call the sat solver
                if sat
                    then putStrLn "1" -- write 1 if the formula is satisfiable
                    else putStrLn "0" -- write 0 if the formula is not satisfiable
                return 0
