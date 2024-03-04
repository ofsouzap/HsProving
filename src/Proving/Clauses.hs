{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Proving.Clauses
  ( -- * Clause Data
    -- $construction
    ClauseLit(..)
  , Clause(..)
  , emptyClause
  , fromCnfTerm
  , ClauseSet(..)
  , fromCnfProposition
    -- * Provers
    -- $provers
  , dpll )
  where

import Control.Applicative
  ( (<|>) )
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( fromList
  , toList
  , empty
  , insert
  , filter
  , member
  , size
  , findMin
  , null
  , foldr )
import qualified Data.List.NonEmpty as NonEmpty
  ( toList )
import Proving.Propositions
  ( Varname
  , NegAtom(..)
  , CnfTerm(..)
  , CnfProposition(..) )

-- $construction
--
-- Data structures and construction functions for clauses and sets of clauses.

-- | A literal in a clause. Either negated or positive.
newtype ClauseLit = ClauseLit (Bool, Varname)
  deriving ( Eq, Ord )

instance Show ClauseLit where
  show (ClauseLit (truth, var)) = if truth then show var else "¬" ++ show var

negateClauseLit :: ClauseLit -> ClauseLit
negateClauseLit (ClauseLit (val, var)) = ClauseLit (not val, var)

-- | A single clause containing a set of possibly negated atoms
newtype Clause = Clause (Set ClauseLit)
  deriving ( Eq, Ord )

instance Show Clause where
  show (Clause xs) = (show . Set.toList) xs

-- | The empty clause. Impossible to satisfy.
emptyClause :: Clause
emptyClause = Clause Set.empty

-- | Create a single clause from a term in a CNF representation of a proposition
fromCnfTerm :: CnfTerm -> Clause
fromCnfTerm (CnfTerm xs) = (Clause . foldr addVal Set.empty) xs where
  addVal (NegAtomConst True) next = next
  addVal (NegAtomConst False) _ = Set.empty
  addVal (NegAtomVar var) next = Set.insert (ClauseLit (True, var)) next
  addVal (NegAtomNegVar var) next = Set.insert (ClauseLit (False, var)) next

-- | A set of clauses.
newtype ClauseSet = ClauseSet (Set Clause)
  deriving ( Eq )

instance Show ClauseSet where
  show (ClauseSet xs) = (show . Set.toList) xs

-- | Create a set of clauses from a CNF representation of a proposition
fromCnfProposition :: CnfProposition -> ClauseSet
fromCnfProposition (CnfProposition terms) = (ClauseSet . Set.fromList . NonEmpty.toList . fmap fromCnfTerm) terms

-- $provers
--
-- Proving algorithms using clauses

-- | Intermediate state of the DPLL algorithm containing the current set of clauses and the set of literals (negated or positive) that are true.
-- N.B. It should always be that literals appearing in the set of true literals don't appear in the clause set
type DpllState = (ClauseSet, Set ClauseLit)

clauseIsTautological :: Clause -> Bool
clauseIsTautological (Clause xs) = any check xs where
  check (ClauseLit (val, var)) = ClauseLit (not val, var) `Set.member` xs

removeTautologicalClauses :: ClauseSet -> ClauseSet
removeTautologicalClauses (ClauseSet xs) = (ClauseSet . Set.filter (not . clauseIsTautological)) xs

removeTautologicalClausesInState :: DpllState -> DpllState
removeTautologicalClausesInState (clauses, vals) = (removeTautologicalClauses clauses, vals)

-- | Try to perform a unit propagation.
-- If none can be performed then Nothing is returned.
tryUnitPropagate :: DpllState -> Maybe DpllState
tryUnitPropagate startState@(ClauseSet startClauses, _) = propagateUnit startState <$> findUnit startClauses where
  findUnit :: Set Clause -> Maybe ClauseLit
  findUnit = foldr findUnitAux Nothing
  findUnitAux :: Clause -> Maybe ClauseLit -> Maybe ClauseLit
  findUnitAux (Clause clause) next = if Set.size clause == 1
    then (Just . Set.findMin) clause
    else next

  propagateUnit :: DpllState -> ClauseLit -> DpllState
  propagateUnit (clauseSet, vals) unit = (propagateUnitInClauseSet unit clauseSet, unit `Set.insert` vals)

-- | Propagate the specified unit through a set of clauses.
propagateUnitInClauseSet :: ClauseLit -> ClauseSet -> ClauseSet
propagateUnitInClauseSet unit (ClauseSet clauses) = (ClauseSet . Set.foldr aux Set.empty) clauses where
  aux :: Clause -> Set Clause -> Set Clause
  aux clause next = case propagateUnitInClause unit clause of
    Nothing -> next
    Just clause' -> clause' `Set.insert` next

-- | Propagate the specified unit through a single clause.
-- If the clause should still exist after this then the changed value is returned, otherwise Nothing is returned.
propagateUnitInClause :: ClauseLit -> Clause -> Maybe Clause
propagateUnitInClause unit (Clause lits) = Clause <$> foldr (propagateUnitInClauseAux unit) (Just Set.empty) lits where
  propagateUnitInClauseAux :: ClauseLit -> ClauseLit -> Maybe (Set ClauseLit) -> Maybe (Set ClauseLit)
  propagateUnitInClauseAux (ClauseLit (unitVal, unitVar)) x@(ClauseLit (xVal, xVar)) next = if unitVar == xVar
    then ( if unitVal == xVal then Nothing else next )
    else Set.insert x <$> next

-- | Try perform a case split on a literal.
-- If no literals remain, return the result of the DPLL process: Nothing if the clauses are unsatisfiable or the set of true literals to satisfy the clauses
tryCaseSplit :: DpllState -> Maybe (Set ClauseLit)
tryCaseSplit (ClauseSet startClauses, startVals) = if Set.null startClauses
  then Just startVals
  else aux (Set.findMin startClauses) where
    aux :: Clause -> Maybe (Set ClauseLit)
    aux (Clause lits) = if Set.null lits
      then Nothing
      else performSplit (Set.findMin lits)

    performSplit :: ClauseLit -> Maybe (Set ClauseLit)
    performSplit lit =
      let trueLit = lit in
      let falseLit = negateClauseLit lit in
      let trueCase = ((propagateUnitInClauseSet trueLit . ClauseSet) startClauses, trueLit `Set.insert` startVals) in
      let falseCase = ((propagateUnitInClauseSet falseLit . ClauseSet) startClauses, falseLit `Set.insert` startVals) in
      let recTrue = dpll' trueCase in
      let recFalse = dpll' falseCase in
        (recTrue <|> recFalse)

dpll' :: DpllState -> Maybe (Set ClauseLit)
dpll' = unitPropStage . removeTautologicalClausesInState where
  unitPropStage :: DpllState -> Maybe (Set ClauseLit)
  unitPropStage state = maybe (tryCaseSplit state) dpll' (tryUnitPropagate state)

-- | Apply the DPLL (Davis-Putnam-Logeman-Loveland) method to a set of clauses to try and find a contradiction to the clause set.
-- If a contradiction is found, this means that the clause set is unsatisfiable and Nothing is returned.
-- If a satisfying valuation is found, this is returned.
dpll :: ClauseSet -> Maybe (Set ClauseLit)
dpll clauseSet = dpll' (clauseSet, Set.empty)
