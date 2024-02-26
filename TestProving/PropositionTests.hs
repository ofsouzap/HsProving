{-# LANGUAGE ScopedTypeVariables #-}
module PropositionTests where

import Test.Hspec
  ( Spec
  , describe
  , it )
import Test.QuickCheck
  ( property
  , Gen )
import Proving.Propositions

prop_evalEquiv_propositionNnf :: Proposition -> Gen Bool
prop_evalEquiv_propositionNnf (prop :: Proposition) = do
  env <- arbitraryEnvForProp prop
  let propEval = evaluate env prop
  let nnfEval = evaluate env (fromProposition prop :: NnfProposition)
  return (propEval == nnfEval)

prop_evalEquiv_nnfCnf :: NnfProposition -> Gen Bool
prop_evalEquiv_nnfCnf (nnf :: NnfProposition) = do
  env <- arbitraryEnvForProp nnf
  let nnfEval = evaluate env nnf
  let cnfEval = (evaluate env . nnfPropositionToCnfProposition) nnf
  return (nnfEval == cnfEval)

prop_evalEquiv_nnfDnf :: NnfProposition -> Gen Bool
prop_evalEquiv_nnfDnf (nnf :: NnfProposition) = do
  env <- arbitraryEnvForProp nnf
  let nnfEval = evaluate env nnf
  let dnfEval = (evaluate env . nnfPropositionToDnfProposition) nnf
  return (nnfEval == dnfEval)

spec :: Spec
spec = do
  describe "Propositions" $ do
    describe "Evaluation Equivalance" $ do
      it "should evaluate basic propositions and NNF propositions equivalently" $ property prop_evalEquiv_propositionNnf
      it "should evaluate NNF propositions and CNF propositions equivalently" $ property prop_evalEquiv_nnfCnf
      it "should evaluate NNF propositions and DNF propositions equivalently" $ property prop_evalEquiv_nnfDnf
