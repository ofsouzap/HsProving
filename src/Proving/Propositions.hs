{-# LANGUAGE InstanceSigs #-}
module Proving.Propositions
  ( -- * Basics #basics#
    -- $basics
    Varname(..)
    -- * Environments #environments#
    -- $environments
  , Env
  , createEnv
  , envEval
  , arbitraryEnvForVars
  , arbitraryEnvForVarStrings
  , arbitraryEnvForProp
    -- * Representation #representations#
    -- $representation
  , Representation(..)
    -- * Basic propositions #basic-propositions#
    -- $basicPropositions
  , Atom(..)
  , Proposition(..)
    -- * Negated Normal Form #nnf#
    -- $nnf
  , NegAtom(..)
  , NnfProposition(..)
    -- * Conjunctive Normal Form #cnf#
    -- $cnf
  , CnfTerm(..)
  , CnfProposition(..)
  , nnfPropositionToCnfProposition
    -- * Disjunctive Normal Form #dnf#
    -- $dnf
  , DnfTerm(..)
  , DnfProposition(..)
  , nnfPropositionToDnfProposition ) where

import qualified Data.Bifunctor as Bifunctor
  ( first )
import Data.List.NonEmpty
  ( NonEmpty((:|)) )
import qualified Data.List.NonEmpty as NonEmpty
  ( toList
  , fromList )
import Data.List
  ( intercalate )
import Data.Set
  ( Set )
import qualified Data.Set as Set
  ( singleton
  , empty
  , toList )
import Test.QuickCheck
  ( sized
  , scale
  , chooseInt
  , vectorOf
  , listOf
  , resize, elements )
import Test.QuickCheck.Arbitrary
  ( Arbitrary
  , arbitrary )
import Test.QuickCheck.Gen
  ( Gen
  , frequency )

bracketWrap :: String -> String
bracketWrap s = "(" ++ s ++ ")"

-- $basics
--
-- Basics for the module

newtype Varname = Varname String
  deriving ( Eq, Ord )

instance Show Varname where
  show (Varname var) = var

instance Arbitrary Varname where
  arbitrary = do
    let letterChars = enumFromTo 'A' 'Z'
    h <- elements letterChars
    ts <- (resize 2 . listOf) (elements letterChars)
    (return . Varname) (h : ts)

-- $environments
--
-- Environments (aka valuations) used for evaluation

-- | Valuations mapping variable names to truth values
newtype Env = Env [(Varname, Bool)]

instance Show Env where
  show (Env xs) = show xs

createEnv :: [(String, Bool)] -> Env
createEnv = Env . map (Bifunctor.first Varname)

envEval :: Varname -> Env -> Maybe Bool
envEval var (Env xs) =
  foldr foldFunc Nothing xs where
    foldFunc (hVar, hVal) next =
      if hVar == var then Just hVal else next

-- | Create an arbitrary environment with a mapping for the given variables.
arbitraryEnvForVars :: [Varname] -> Gen Env
arbitraryEnvForVars vars = do
  vals <- vectorOf (length vars) (arbitrary :: Gen Bool)
  (return . Env) (zip vars vals)

-- | Create an arbitrary environment with a mapping for the given variables.
-- Variable names are given as strings.
arbitraryEnvForVarStrings :: [String] -> Gen Env
arbitraryEnvForVarStrings = arbitraryEnvForVars . map Varname

-- | Create an arbitrary environment with a mapping for the free variables of the given proposition representation.
arbitraryEnvForProp :: Representation r => r -> Gen Env
arbitraryEnvForProp = arbitraryEnvForVars . Set.toList . freeVars

-- $basicPropositions
--
-- Basic propositions that are more human-writable.

-- | A propositional atom
data Atom
  = AtomConst Bool
  | AtomVar Varname
  deriving ( Eq )

instance Show Atom where
  show (AtomConst True) = "t"
  show (AtomConst False) = "f"
  show (AtomVar var) = show var

instance Arbitrary Atom where
  arbitrary = frequency
    [ (1, AtomConst <$> arbitrary)
    , (1, AtomVar <$> arbitrary) ]

evalAtom :: Env -> Atom -> Maybe Bool
evalAtom _ (AtomConst b) = Just b
evalAtom env (AtomVar var) = envEval var env

atomFreeVars :: Atom -> Set Varname
atomFreeVars (AtomConst _) = Set.empty
atomFreeVars (AtomVar var) = Set.singleton var

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

instance Arbitrary Proposition where
  arbitrary = sized genSized where
    genSized :: Int -> Gen Proposition
    genSized n
      | n <= 0 = PropAtom <$> arbitrary
      | otherwise = frequency
        [ (1, PropAtom <$> arbitrary)
        , (1, PropNot <$> scale (max 0 . pred) arbitrary)
        , (1, PropOr <$> genSubPs)
        , (1, PropAnd <$> genSubPs)
        , (1, do
          let scaledArb = scale (max 0 . pred . (`div` 2)) arbitrary
          x <- scaledArb
          PropImpl x <$> scaledArb)
        , (1, do
          let scaledArb = scale (max 0 . pred . (`div` 2)) arbitrary
          x <- scaledArb
          PropBiImpl x <$> scaledArb) ]
    genSubPs :: Gen (NonEmpty Proposition)
    genSubPs = sized $ \ n ->
      if n <= 0 then return <$> arbitrary
      else do
        subCount <- chooseInt (1, n)
        NonEmpty.fromList <$> vectorOf subCount (scale (max 0 . pred . (`div` subCount)) arbitrary)

-- $representation
--
-- A typeclass for different representations of propositions in propositional logic.

-- | The typeclass for representations of propositions in propositional logic.
class Representation a where
  -- | Convert the basic representation of a proposition into the other representation.
  fromProposition :: Proposition -> a
  -- | Evaluate a proposition. If fails to evaluate due to not having a valuation for a variable then returns Nothing.
  -- Due to how evaluation is sometimes performed, this doesn't always detect variables without valuations and will sometimes return a
  -- result if one can be determined without evaluating some variables.
  evaluate :: Env -> a -> Maybe Bool
  -- | Determine the set of free variables.
  freeVars :: a -> Set Varname

instance Representation Proposition where
  fromProposition :: Proposition -> Proposition
  fromProposition = id
  evaluate :: Env -> Proposition -> Maybe Bool
  evaluate env (PropAtom a) = evalAtom env a
  evaluate env (PropNot p) = not <$> evaluate env p
  evaluate env (PropOr ps) = foldr foldFunc (Just False) ps where
    foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
    foldFunc p next = case evaluate env p of
      Nothing -> Nothing
      Just True -> Just True
      Just False -> next
  evaluate env (PropAnd ps) = foldr foldFunc (Just True) ps where
    foldFunc :: Proposition -> Maybe Bool -> Maybe Bool
    foldFunc p next = case evaluate env p of
      Nothing -> Nothing
      Just False -> Just False
      Just True -> next
  evaluate env (PropImpl a b) = evaluate env (PropOr (PropNot a :| [b]))
  evaluate env (PropBiImpl a b) = evaluate env (PropOr (PropAnd (a :| [b]) :| [PropAnd (PropNot a :| [PropNot b])]))
  freeVars :: Proposition -> Set Varname
  freeVars (PropAtom a) = atomFreeVars a
  freeVars (PropNot p) = freeVars p
  freeVars (PropOr ps) = foldr ((<>) . freeVars) Set.empty ps
  freeVars (PropAnd ps) = foldr ((<>) . freeVars) Set.empty ps
  freeVars (PropImpl a b) = freeVars a <> freeVars b
  freeVars (PropBiImpl a b) = freeVars a <> freeVars b

-- $nnf
--
-- Propositions in Negated Normal Form (NNF).

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
  = NegAtomConst Bool
  | NegAtomVar Varname
  | NegAtomNegVar Varname
  deriving ( Eq )

instance Arbitrary NegAtom where
  arbitrary = frequency
    [ (1, NegAtomConst <$> arbitrary)
    , (1, NegAtomNegVar <$> arbitrary)
    , (1, NegAtomVar <$> arbitrary) ]

instance Show NegAtom where
  show (NegAtomConst True) = "t"
  show (NegAtomConst False) = "f"
  show (NegAtomVar var) = show var
  show (NegAtomNegVar var) = "¬" ++ show var

atomToNegAtom :: Atom -> NegAtom
atomToNegAtom (AtomConst b) = NegAtomConst b
atomToNegAtom (AtomVar var) = NegAtomVar var

evalNegAtom :: Env -> NegAtom -> Maybe Bool
evalNegAtom _ (NegAtomConst b) = Just b
evalNegAtom env (NegAtomVar var) = envEval var env
evalNegAtom env (NegAtomNegVar var) = not <$> envEval var env

negAtomFreeVars :: NegAtom -> Set Varname
negAtomFreeVars (NegAtomConst _) = Set.empty
negAtomFreeVars (NegAtomVar var) = Set.singleton var
negAtomFreeVars (NegAtomNegVar var) = Set.singleton var

-- | Propositional logic proposition in NNF (Negated Normal Form)
data NnfProposition
  = NnfAtom NegAtom
  | NnfOr (NonEmpty NnfProposition)
  | NnfAnd (NonEmpty NnfProposition)

instance Show NnfProposition where
  show (NnfAtom a) = show a
  show (NnfOr ps) = (intercalate "+" . NonEmpty.toList .fmap (bracketWrap . show)) ps
  show (NnfAnd ps) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) ps

instance Arbitrary NnfProposition where
  arbitrary = sized genSized where
    genSized :: Int -> Gen NnfProposition
    genSized n
      | n <= 0 = NnfAtom <$> arbitrary
      | otherwise = frequency
        [ (1, NnfAtom <$> arbitrary)
        , (1, NnfOr <$> genSubPs)
        , (1, NnfAnd <$> genSubPs) ]
    genSubPs :: Gen (NonEmpty NnfProposition)
    genSubPs = sized $ \ n ->
      if n <= 0 then return <$> arbitrary
      else do
        subCount <- chooseInt (1, n)
        NonEmpty.fromList <$> vectorOf subCount (scale (max 0 . pred . (`div` subCount)) arbitrary)

simplePropositionToNnfProposition :: SimpleProposition -> NnfProposition
simplePropositionToNnfProposition (SPAtom a) = (NnfAtom . atomToNegAtom) a
simplePropositionToNnfProposition (SPOr ps) = (NnfOr . fmap simplePropositionToNnfProposition) ps
simplePropositionToNnfProposition (SPAnd ps) = (NnfAnd . fmap simplePropositionToNnfProposition) ps
simplePropositionToNnfProposition (SPNot (SPNot p)) = simplePropositionToNnfProposition p
simplePropositionToNnfProposition (SPNot (SPAtom (AtomConst b))) = (NnfAtom . NegAtomConst . not) b
simplePropositionToNnfProposition (SPNot (SPAtom (AtomVar var))) = (NnfAtom . NegAtomNegVar) var
simplePropositionToNnfProposition (SPNot (SPOr ps)) = (NnfAnd . fmap (simplePropositionToNnfProposition . SPNot)) ps
simplePropositionToNnfProposition (SPNot (SPAnd ps)) = (NnfOr . fmap (simplePropositionToNnfProposition . SPNot)) ps

instance Representation NnfProposition where
  fromProposition :: Proposition -> NnfProposition
  fromProposition = simplePropositionToNnfProposition . propositionToSimpleProposition
  evaluate :: Env -> NnfProposition -> Maybe Bool
  evaluate env (NnfAtom a) = evalNegAtom env a
  evaluate env (NnfOr ps) = foldr foldFunc (Just False) ps where
    foldFunc :: NnfProposition -> Maybe Bool -> Maybe Bool
    foldFunc p next = case evaluate env p of
      Nothing -> Nothing
      Just True -> Just True
      Just False -> next
  evaluate env (NnfAnd ps) = foldr foldFunc (Just True) ps where
    foldFunc :: NnfProposition -> Maybe Bool -> Maybe Bool
    foldFunc p next = case evaluate env p of
      Nothing -> Nothing
      Just False -> Just False
      Just True -> next
  freeVars :: NnfProposition -> Set Varname
  freeVars (NnfAtom a) = negAtomFreeVars a
  freeVars (NnfOr ps) = foldr ((<>) . freeVars) Set.empty ps
  freeVars (NnfAnd ps) = foldr ((<>) . freeVars) Set.empty ps

-- $cnf
--
-- Propositions in Conjunctive Normal Form (CNF)

newtype CnfTerm = CnfTerm (NonEmpty NegAtom)

unwrapCnfTerm :: CnfTerm -> NonEmpty NegAtom
unwrapCnfTerm (CnfTerm xs) = xs

instance Show CnfTerm where
  show (CnfTerm xs) = (intercalate "+" . NonEmpty.toList . fmap (bracketWrap . show)) xs

instance Arbitrary CnfTerm where
  arbitrary = sized $ \ n' -> do
    n <- chooseInt (1, n')
    CnfTerm . NonEmpty.fromList <$> vectorOf n arbitrary

newtype CnfProposition = CnfProposition (NonEmpty CnfTerm)

unwrapCnfProposition :: CnfProposition -> NonEmpty CnfTerm
unwrapCnfProposition (CnfProposition xs) = xs

instance Show CnfProposition where
  show (CnfProposition xs) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) xs

instance Arbitrary CnfProposition where
  arbitrary = sized $ \ n' -> do
    n <- chooseInt (1, n')
    CnfProposition . NonEmpty.fromList <$> (vectorOf n . scale (`div` n)) arbitrary

-- | Convert a proposition in NNF into a proposition in CNF
nnfPropositionToCnfProposition :: NnfProposition -> CnfProposition
nnfPropositionToCnfProposition (NnfAtom a) = (CnfProposition . pure . CnfTerm . pure) a
nnfPropositionToCnfProposition (NnfAnd ps) = CnfProposition (ps >>= unwrapCnfProposition . nnfPropositionToCnfProposition)
nnfPropositionToCnfProposition (NnfOr ps) = (CnfProposition . fmap CnfTerm . fuseAll) (fmap unwrapCnfTerm . unwrapCnfProposition . nnfPropositionToCnfProposition <$> ps) where
  fuseTwo :: NonEmpty (NonEmpty NegAtom) -> NonEmpty (NonEmpty NegAtom) -> NonEmpty (NonEmpty NegAtom)
  fuseTwo xs ys = do
    x <- xs
    y <- ys
    return (x <> y)
  fuseAll :: NonEmpty (NonEmpty (NonEmpty NegAtom)) -> NonEmpty (NonEmpty NegAtom)
  fuseAll (h :| ts) = foldr fuseTwo h ts

instance Representation CnfProposition where
  fromProposition :: Proposition -> CnfProposition
  fromProposition = nnfPropositionToCnfProposition . fromProposition
  evaluate :: Env -> CnfProposition -> Maybe Bool
  evaluate env (CnfProposition terms) = foldr foldPropFunc (Just True) terms where
    foldPropFunc :: CnfTerm -> Maybe Bool -> Maybe Bool
    foldPropFunc term next = case evalTerm term of
      Nothing -> Nothing
      Just False -> Just False
      Just True -> next
    evalTerm :: CnfTerm -> Maybe Bool
    evalTerm (CnfTerm atoms) = foldr foldTermFunc (Just False) atoms
    foldTermFunc :: NegAtom -> Maybe Bool -> Maybe Bool
    foldTermFunc p next = case evalNegAtom env p of
      Nothing -> Nothing
      Just True -> Just True
      Just False -> next
  freeVars :: CnfProposition -> Set Varname
  freeVars (CnfProposition terms) = foldr ((<>) . getTermVars) Set.empty terms where
    getTermVars :: CnfTerm -> Set Varname
    getTermVars = foldr ((<>) . negAtomFreeVars) Set.empty . unwrapCnfTerm

-- $dnf
--
-- Propositions in Disjunctive Normal Form (DNF)

newtype DnfTerm = DnfTerm (NonEmpty NegAtom)

unwrapDnfTerm :: DnfTerm -> NonEmpty NegAtom
unwrapDnfTerm (DnfTerm xs) = xs

instance Show DnfTerm where
  show (DnfTerm xs) = (intercalate "." . NonEmpty.toList . fmap (bracketWrap . show)) xs

instance Arbitrary DnfTerm where
  arbitrary = sized $ \ n' -> do
    n <- chooseInt (1, n')
    DnfTerm . NonEmpty.fromList <$> vectorOf n arbitrary

newtype DnfProposition = DnfProposition (NonEmpty DnfTerm)

unwrapDnfProposition :: DnfProposition -> NonEmpty DnfTerm
unwrapDnfProposition (DnfProposition xs) = xs

instance Show DnfProposition where
  show (DnfProposition xs) = (intercalate "+" . NonEmpty.toList . fmap (bracketWrap . show)) xs

instance Arbitrary DnfProposition where
  arbitrary = sized $ \ n' -> do
    n <- chooseInt (1, n')
    DnfProposition . NonEmpty.fromList <$> (vectorOf n . scale (`div` n)) arbitrary

-- | Convert a proposition in NNF into a proposition in DNF
nnfPropositionToDnfProposition :: NnfProposition -> DnfProposition
nnfPropositionToDnfProposition (NnfAtom a) = (DnfProposition . pure . DnfTerm . pure) a
nnfPropositionToDnfProposition (NnfOr ps) = DnfProposition (ps >>= unwrapDnfProposition . nnfPropositionToDnfProposition)
nnfPropositionToDnfProposition (NnfAnd ps) = (DnfProposition . fmap DnfTerm . fuseAll) (fmap unwrapDnfTerm . unwrapDnfProposition . nnfPropositionToDnfProposition <$> ps) where
  fuseTwo :: NonEmpty (NonEmpty NegAtom) -> NonEmpty (NonEmpty NegAtom) -> NonEmpty (NonEmpty NegAtom)
  fuseTwo xs ys = do
    x <- xs
    y <- ys
    return (x <> y)
  fuseAll :: NonEmpty (NonEmpty (NonEmpty NegAtom)) -> NonEmpty (NonEmpty NegAtom)
  fuseAll (h :| ts) = foldr fuseTwo h ts

instance Representation DnfProposition where
  fromProposition :: Proposition -> DnfProposition
  fromProposition = nnfPropositionToDnfProposition . fromProposition
  evaluate :: Env -> DnfProposition -> Maybe Bool
  evaluate env (DnfProposition terms) = foldr foldPropFunc (Just False) terms where
    foldPropFunc :: DnfTerm -> Maybe Bool -> Maybe Bool
    foldPropFunc term next = case evalTerm term of
      Nothing -> Nothing
      Just True -> Just True
      Just False -> next
    evalTerm :: DnfTerm -> Maybe Bool
    evalTerm (DnfTerm atoms) = foldr foldTermFunc (Just True) atoms
    foldTermFunc :: NegAtom -> Maybe Bool -> Maybe Bool
    foldTermFunc p next = case evalNegAtom env p of
      Nothing -> Nothing
      Just False -> Just False
      Just True -> next
  freeVars :: DnfProposition -> Set Varname
  freeVars (DnfProposition terms) = foldr ((<>) . getTermVars) Set.empty terms where
    getTermVars :: DnfTerm -> Set Varname
    getTermVars = foldr ((<>) . negAtomFreeVars) Set.empty . unwrapDnfTerm
