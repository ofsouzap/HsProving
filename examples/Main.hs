module Main where

import Data.List.NonEmpty ( NonEmpty((:|)) )
import Proving.Propositions

main :: IO ()
main = do
  let p = Impl (And (Atom (Var "P") :| [Atom (Var "Q")])) (Not (Atom (Var "Q")))
  print p
  let env1 = createEnv [("P", True), ("Q", False)]
  (print . evaluateProposition env1) p
  let env2 = createEnv [("P", True), ("Q", True)]
  (print . evaluateProposition env2) p
  let env3 = createEnv [("P", False)]
  (print . evaluateProposition env3) p
  let env4 = createEnv [("P", True)]
  (print . evaluateProposition env4) p
