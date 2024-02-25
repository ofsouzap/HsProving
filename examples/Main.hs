module Main where

import Data.List.NonEmpty ( NonEmpty((:|)) )
import Proving.Propositions

main :: IO ()
main = do
  let p = PropImpl (PropAnd (PropAtom (AtomVar "P") :| [PropAtom (AtomVar "Q")])) (PropNot (PropAtom (AtomVar "Q")))
  print p
  let env1 = createEnv [("P", True), ("Q", False)]
  print "Eval {P, !Q}:"
  (print . evaluateProposition env1) p
  let env2 = createEnv [("P", True), ("Q", True)]
  print "Eval {P, Q}:"
  (print . evaluateProposition env2) p
  let env3 = createEnv [("P", False)]
  print "Eval {!P}:"
  (print . evaluateProposition env3) p
  let env4 = createEnv [("P", True)]
  print "Eval {P}:"
  (print . evaluateProposition env4) p
  print "Nnf:"
  (print . propositionToNnfProposition) p
