module Main where

import Proving.Propositions
import Proving.Propositions.Shorthand

main :: IO ()
main = do
  -- let p = pimpl (pand [pvar "P", pvar "Q"]) (pnot (pvar "Q"))
  -- let p = por [pand [pvar "A", pvar "B", pvar "C"], pand [pvar "D", pvar "E"]]
  let p = pand [por [pvar "A", pvar "B", pvar "C"], por [pvar "D", pvar "E"]]
  print p
  let env1 = createEnv [("P", True), ("Q", False)]
  putStrLn "Eval {P, !Q}:"
  (print . evaluateProposition env1) p
  let env2 = createEnv [("P", True), ("Q", True)]
  putStrLn "Eval {P, Q}:"
  (print . evaluateProposition env2) p
  let env3 = createEnv [("P", False)]
  putStrLn "Eval {¬P}:"
  (print . evaluateProposition env3) p
  let env4 = createEnv [("P", True)]
  putStrLn "Eval {P}:"
  (print . evaluateProposition env4) p
  putStrLn "NNF:"
  (print . propositionToNnfProposition) p
  putStrLn "CNF:"
  (print . propositionToCnfProposition) p
  putStrLn "DNF:"
  (print . propositionToDnfProposition) p
