module Proving.Propositions
  ( Varname
  , Env
  , createEnv
  , envEval
  , Atom(..)
  , Proposition(..)
  , evaluateProposition
  , NegAtom(..)
  , NnfProposition(..)
  , propositionToNnfProposition ) where

import Data.List.NonEmpty
  ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty as NonEmpty
  ( toList )
import Data.List
  ( intercalate )

bracketWrap :: String -> String
bracketWrap s = "(" ++ s ++ ")"

type Varname = String

-- Environments

-- | Valuations mapping variable names to truth values
newtype Env = Env [(Varname, Bool)]

createEnv :: [(Varname, Bool)] -> Env
createEnv = Env

envEval :: Varname -> Env -> Maybe Bool
envEval var (Env xs) =
  foldr foldFunc Nothing xs where
    foldFunc (hVar, hVal) next =
      if hVar == var then Just hVal else next

-- Propositions

-- | A propositional atom
data Atom
  = AtomLit Bool
  | AtomVar Varname
  deriving ( Eq )

instance Show Atom where
  show (AtomLit True) = "t"
  show (AtomLit False) = "f"
  show (AtomVar var) = var

-- | A proposition of propositional logic
data Proposition
  = PropAtom Atom
  | PropNot Proposition
  | PropOr (NonEmpty Proposition)
  | PropAnd (NonEmpty Proposition)
  | PropImpl Proposition Proposition
  | PropBiImpl Proposition Proposition

instance Show Proposition where
  show (PropAtom a) = show a
  show (PropNot p) = "¬" ++ (bracketWrap . show) p
  show (PropOr ps) = (intercalate "+" . NonEmpty.toList .fmap (bracketWrap . show)) ps
  show (PropAnd ps) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) ps
  show (PropImpl a b) = (bracketWrap . show) a ++ "->" ++ (bracketWrap . show) b
  show (PropBiImpl a b) = (bracketWrap . show) a ++ "<->" ++ (bracketWrap . show) b

-- | Evaluate a proposition. If fails to evaluate due to not having a valuation for a variable then returns Nothing.
-- Due to how evaluation is performed, this doesn't always detect variables without valuations and will sometimes return a
-- result if one can be determined without evaluating some variables.
evaluateProposition :: Env -> Proposition -> Maybe Bool
evaluateProposition _ (PropAtom (AtomLit b)) = Just b
evaluateProposition env (PropAtom (AtomVar var)) = envEval var env
evaluateProposition env (PropNot p) = not <$> evaluateProposition env p
evaluateProposition env (PropOr ps) = foldr foldFunc (Just False) ps where
  foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
  foldFunc p next = case evaluateProposition env p of
    Nothing -> Nothing
    Just True -> Just True
    Just False -> next
evaluateProposition env (PropAnd ps) = foldr foldFunc (Just True) ps where
  foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
  foldFunc p next = case evaluateProposition env p of
    Nothing -> Nothing
    Just False -> Just False
    Just True -> next
evaluateProposition env (PropImpl a b) = evaluateProposition env (PropOr (PropNot a :| [b]))
evaluateProposition env (PropBiImpl a b) = evaluateProposition env (PropOr (PropAnd (a :| [b]) :| [PropAnd (PropNot a :| [PropNot b])]))

-- NNF

-- | Propositional logic proposition without implication
data SimpleProposition
  = SPAtom Atom
  | SPNot SimpleProposition
  | SPOr (NonEmpty SimpleProposition)
  | SPAnd (NonEmpty SimpleProposition)

propositionToSimpleProposition :: Proposition -> SimpleProposition
propositionToSimpleProposition (PropAtom a) = SPAtom a
propositionToSimpleProposition (PropNot p) = (SPNot . propositionToSimpleProposition) p
propositionToSimpleProposition (PropOr ps) = (SPOr . fmap propositionToSimpleProposition) ps
propositionToSimpleProposition (PropAnd ps) = (SPAnd . fmap propositionToSimpleProposition) ps
propositionToSimpleProposition (PropImpl a b) = SPOr ((SPNot . propositionToSimpleProposition) a :| [propositionToSimpleProposition b])
propositionToSimpleProposition (PropBiImpl a b) = SPOr
  ( SPAnd (propositionToSimpleProposition a :| [propositionToSimpleProposition b])
  :| [SPAnd ((SPNot . propositionToSimpleProposition) a :| [(SPNot . propositionToSimpleProposition) b])] )

-- | Atomic value containing negation information
data NegAtom
  = NegAtomLit Bool
  | NegAtomVar Varname
  | NegAtomNegVar Varname

atomToNegAtom :: Atom -> NegAtom
atomToNegAtom (AtomLit b) = NegAtomLit b
atomToNegAtom (AtomVar var) = NegAtomVar var

-- | Propositional logic proposition in NNF (Negated Normal Form)
data NnfProposition
  = NnfAtom NegAtom
  | NnfOr (NonEmpty NnfProposition)
  | NnfAnd (NonEmpty NnfProposition)

instance Show NnfProposition where
  show (NnfAtom (NegAtomLit b)) = show b
  show (NnfAtom (NegAtomVar var)) = var
  show (NnfAtom (NegAtomNegVar var)) = "¬" ++ show var
  show (NnfOr ps) = (intercalate "+" . NonEmpty.toList .fmap (bracketWrap . show)) ps
  show (NnfAnd ps) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) ps

simplePropositionToNnfProposition :: SimpleProposition -> NnfProposition
simplePropositionToNnfProposition (SPAtom a) = (NnfAtom . atomToNegAtom) a
simplePropositionToNnfProposition (SPOr ps) = (NnfOr . fmap simplePropositionToNnfProposition) ps
simplePropositionToNnfProposition (SPAnd ps) = (NnfAnd . fmap simplePropositionToNnfProposition) ps
simplePropositionToNnfProposition (SPNot (SPNot p)) = simplePropositionToNnfProposition p
simplePropositionToNnfProposition (SPNot (SPAtom (AtomLit b))) = (NnfAtom . NegAtomLit . not) b
simplePropositionToNnfProposition (SPNot (SPAtom (AtomVar var))) = (NnfAtom . NegAtomNegVar) var
simplePropositionToNnfProposition (SPNot (SPOr ps)) = (NnfAnd . fmap (simplePropositionToNnfProposition . SPNot)) ps
simplePropositionToNnfProposition (SPNot (SPAnd ps)) = (NnfOr . fmap (simplePropositionToNnfProposition . SPNot)) ps

-- | Convert a raw proposition to a proposition in NNF (Negated Normal Form)
propositionToNnfProposition :: Proposition -> NnfProposition
propositionToNnfProposition = simplePropositionToNnfProposition . propositionToSimpleProposition
