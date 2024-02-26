module Proving.Clauses
  ( ClauseLit(..)
  , Clause(..)
  , emptyClause
  , fromDnfTerm
  , ClauseSet(..)
  , fromDnfProposition ) where

import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( fromList
  , toList
  , empty
  , insert )
import qualified Data.List.NonEmpty as NonEmpty
  ( toList )
import Proving.Propositions
  ( Varname
  , NegAtom(..)
  , DnfTerm(..)
  , DnfProposition(..) )

-- | A literal in a clause. Either negated or positive.
data ClauseLit
  = ClauseLit Varname
  | ClauseNegLit Varname
  deriving ( Eq, Ord )

instance Show ClauseLit where
  show (ClauseLit var) = show var
  show (ClauseNegLit var) = show var

-- | A single clause containing a set of possibly negated atoms
newtype Clause = Clause (Set ClauseLit)
  deriving ( Eq, Ord )

instance Show Clause where
  show (Clause xs) = (show . Set.toList) xs

-- | The empty clause. Impossible to satisfy.
emptyClause :: Clause
emptyClause = Clause Set.empty

-- | Create a single clause from a term in a DNF representation of a proposition
fromDnfTerm :: DnfTerm -> Clause
fromDnfTerm (DnfTerm xs) = (Clause . foldr addVal Set.empty) xs where
  addVal (NegAtomConst True) next = next
  addVal (NegAtomConst False) _ = Set.empty
  addVal (NegAtomVar var) next = Set.insert (ClauseLit var) next
  addVal (NegAtomNegVar var) next = Set.insert (ClauseNegLit var) next

-- | A set of clauses.
newtype ClauseSet = ClauseSet (Set Clause)
  deriving ( Eq )

instance Show ClauseSet where
  show (ClauseSet xs) = (show . Set.toList) xs

-- | Create a set of clauses from a DNF representation of a proposition
fromDnfProposition :: DnfProposition -> ClauseSet
fromDnfProposition (DnfProposition terms) = (ClauseSet . Set.fromList . NonEmpty.toList . fmap fromDnfTerm) terms
