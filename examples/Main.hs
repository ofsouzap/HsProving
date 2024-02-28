module Main where

import Proving.Propositions
import Proving.Propositions.Shorthand
import Proving.Clauses

main :: IO ()
main = do
  -- let p = pimpl (pand [pvar "A", pvar "B"]) (pnot (pvar "B"))
  let p = por [pand [pvar "A", pvar "B", pvar "C"], pand [pvar "D", pvar "E"]]
  -- let p = pand [por [pvar "A", pvar "B", pvar "C"], por [pvar "D", pvar "E"]]
  print p
  let env1 = createEnv [("A", True), ("B", False)]
  putStrLn "Eval {P, !Q}:"
  (print . evaluate env1) p
  let env2 = createEnv [("A", True), ("B", True)]
  putStrLn "Eval {P, Q}:"
  (print . evaluate env2) p
  let env3 = createEnv [("A", False)]
  putStrLn "Eval {¬P}:"
  (print . evaluate env3) p
  let env4 = createEnv [("A", True)]
  putStrLn "Eval {P}:"
  (print . evaluate env4) p
  putStrLn "NNF:"
  let nnf = fromProposition p :: NnfProposition
  print nnf
  (print . evaluate env1) nnf
  putStrLn "CNF:"
  let cnf = fromProposition p :: CnfProposition
  print cnf
  (print . evaluate env1) cnf
  putStrLn "DNF:"
  let dnf = fromProposition p :: DnfProposition
  print dnf
  (print . evaluate env1) dnf
  let clause = (fromCnfProposition . fromProposition) p
  putStrLn "Clause:"
  print clause
  putStrLn "DPLL on clause:"
  print (dpll clause)
