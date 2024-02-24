module Proving.Propositions
  ( Varname
  , Env
  , createEnv
  , envEval
  , Atom(..)
  , Proposition(..)
  , evaluateProposition ) where

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
  = Lit Bool
  | Var Varname
  deriving ( Eq )

instance Show Atom where
  show (Lit True) = "t"
  show (Lit False) = "f"
  show (Var var) = var

-- | A proposition of propositional logic
data Proposition
  = Atom Atom
  | Not Proposition
  | Or (NonEmpty Proposition)
  | And (NonEmpty Proposition)
  | Impl Proposition Proposition
  | BiImpl Proposition Proposition

instance Show Proposition where
  show (Atom a) = show a
  show (Not p) = "¬" ++ (bracketWrap . show) p
  show (Or ps) = (intercalate "+" . NonEmpty.toList .fmap (bracketWrap . show)) ps
  show (And ps) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) ps
  show (Impl a b) = (bracketWrap . show) a ++ "->" ++ (bracketWrap . show) b
  show (BiImpl a b) = (bracketWrap . show) a ++ "<->" ++ (bracketWrap . show) b

-- | Evaluate a proposition. If fails to evaluate due to not having a valuation for a variable then returns Nothing.
-- Due to how evaluation is performed, this doesn't always detect variables without valuations and will sometimes return a
-- result if one can be determined without evaluating some variables.
evaluateProposition :: Env -> Proposition -> Maybe Bool
evaluateProposition _ (Atom (Lit b)) = Just b
evaluateProposition env (Atom (Var var)) = envEval var env
evaluateProposition env (Not p) = not <$> evaluateProposition env p
evaluateProposition env (Or ps) = foldr foldFunc (Just False) ps where
  foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
  foldFunc p next = case evaluateProposition env p of
    Nothing -> Nothing
    Just True -> Just True
    Just False -> next
evaluateProposition env (And ps) = foldr foldFunc (Just True) ps where
  foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
  foldFunc p next = case evaluateProposition env p of
    Nothing -> Nothing
    Just False -> Just False
    Just True -> next
evaluateProposition env (Impl a b) = evaluateProposition env (Or (Not a :| [b]))
evaluateProposition env (BiImpl a b) = evaluateProposition env (Or (And (a :| [b]) :| [And (Not a :| [Not b])]))
