module Proving.Propositions.Shorthand
  ( plit
  , pvar
  , pnot
  , por
  , pand
  , pimpl
  , pbiimpl ) where

import qualified Data.List.NonEmpty as NonEmpty
  ( fromList )
import Proving.Propositions

-- | A literal in a proposition
plit :: Bool -> Proposition
plit = PropAtom . AtomLit

-- | A variable in a proposition
pvar :: String -> Proposition
pvar = PropAtom . AtomVar . Varname

-- | Negate a proposition
pnot :: Proposition -> Proposition
pnot = PropNot

-- | Unsafe shorthand for creating a disjunction from a list.
-- The list must be non-empty or this creates an error.
por :: [Proposition] -> Proposition
por = PropOr . NonEmpty.fromList

-- | Unsafe shorthand for creating a conjunction from a list.
-- The list must be non-empty or this creates an error.
pand :: [Proposition] -> Proposition
pand = PropAnd . NonEmpty.fromList

-- | An implication proposition
pimpl :: Proposition -> Proposition -> Proposition
pimpl = PropImpl

-- | An bi-implication proposition
pbiimpl :: Proposition -> Proposition -> Proposition
pbiimpl = PropBiImpl
