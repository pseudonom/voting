{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Voting where

import Control.Lens
import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.List as List
import Data.Maybe (fromJust, fromMaybe)
import Data.Semigroup (Semigroup, (<>))
import Debug.Trace (trace)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Test.QuickCheck (Arbitrary(..), Result, vector, quickCheckResult, arbitraryBoundedEnum)

type Ballot f t b a = f (Identified t a b)
type UrBallot t a = Ballot HashSet t Double a

data Identified t a b
  = I
  { _identifier :: a
  , _value :: b
  } deriving (Show, Eq, Generic, Hashable)
makeLenses ''Identified

-- | Ballots should be exhaustive and non-repetitive
checkCompleteBallot :: forall f t a b. (Foldable f, Eq a, Enum a, Bounded a) => f (Identified t a b) -> Bool
checkCompleteBallot as
  | uniqSize == size && uniqSize == cardinality = True
  | otherwise = False
    where
      uniqSize = Foldable.length . List.nubBy ((==) `on` view identifier) . Foldable.toList $ as
      size = Foldable.length as
      cardinality = Foldable.length (enumFromTo minBound maxBound :: [a])


newtype CompleteBallot f t b a
  = CompleteBallot
  { unCompleteBallot :: Ballot f t b a
  }
type CompleteUrBallot t a = CompleteBallot HashSet t Double a
deriving instance (Eq (Ballot f t b a)) => Eq (CompleteBallot f t b a)
deriving instance (Show (Ballot f t b a)) => Show (CompleteBallot f t b a)

mkCompleteBallot :: (Foldable f, Bounded a, Enum a, Eq a) => Ballot f t b a -> Maybe (CompleteBallot f t b a)
mkCompleteBallot ballot
  | checkCompleteBallot ballot = Just . CompleteBallot $ ballot
  | otherwise = Nothing

type PollingRule g c = forall a. UrBallot "candidate" a -> g (Identified "candidate" a c)
type RankVote g = PollingRule g ()

type AggregationRule pid g b h =
  forall cid. (Eq cid, Hashable cid) => [Identified "voter" pid (g (Identified "candidate" cid b))] -> h (HashSet cid)
type RankAggregationRule pid g b h = AggregationRule pid [] () h
type SocialWelfareFunction pid g b = AggregationRule pid g b []
type SocialChoiceFunction pid g b = AggregationRule pid g b Identity
type AnonymousAggregationRule g b h = forall pid. AggregationRule pid g b h
type AnonymousSocialWelfareFunction g b = forall pid. AggregationRule pid g b []
type AnonymousRankSocialWelfareFunction g = forall pid. AggregationRule pid g () []

type VotingSystem pid cid h = [Identified "voter" pid (UrBallot "candidate" cid)] -> h (HashSet cid)

combine
  :: forall cid pid g c h
  . (Eq cid, Hashable cid, Semigroup (h (HashSet cid)), Applicative h, Foldable h)
  => PollingRule g c
  -> AggregationRule pid g c h
  -> HashSet cid
  -> VotingSystem pid cid h
combine poll aggregate choices votes
  | null candidatesWithoutVotes = voteResults
  | otherwise = voteResults <> pure candidatesWithoutVotes
    where
      candidatesWithoutVotes = choices `Set.difference` candidatesWithVotes
      candidatesWithVotes = Set.fromList $ Foldable.toList voteResults >>= Foldable.toList
      voteResults = aggregate . fmap (over value poll) $ votes



pluralityPoll :: RankVote Identity
pluralityPoll prefs = Identity $ Foldable.maximumBy (compare `on` view value) prefs & value .~ ()

pluralityAggregate :: AnonymousRankSocialWelfareFunction Identity
pluralityAggregate ballots =
  fmap (Set.fromList . fmap (view identifier . fst)) . List.groupBy ((==) `on` snd) . reverse . toAscOccurList . toCountMap $ view (value . identity) <$> ballots

toCountMap :: (Eq a, Hashable a) => [a] -> HashMap a Natural
toCountMap = Map.fromListWith (+) . map (\a -> (a, 1))

toAscOccurList :: HashMap a Natural -> [(a, Natural)]
toAscOccurList = List.sortOn snd . Map.toList

plurality
  :: forall cid pid
  . (Eq cid, Hashable cid)
  => HashSet cid
  -> [Identified "voter" pid (UrBallot "candidate" cid)]
  -> [HashSet cid]
plurality = combine pluralityPoll pluralityAggregate


data Candidate = Alice | Bob | Eve deriving (Bounded, Enum, Eq, Generic, Hashable, Show)

voter1, voter2, voter3 :: Identified "voter" String (UrBallot "candidate" Candidate)
voter1 = I "voter1" . Set.fromList $ [I Alice 0, I Bob 1, I Eve 4]
voter2 = I "voter2" . Set.fromList $ [I Alice 0, I Bob 1, I Eve 0]
voter3 = I "voter3" . Set.fromList $ [I Alice 0, I Bob 1, I Eve 1]

votes :: [Identified "voter" String (UrBallot "candidate" Candidate)]
votes = [voter1, voter2, voter3]



nonEmptyPowerset :: [b] -> [[b]]
nonEmptyPowerset = List.filter (not . null) . Monad.filterM (const [True, False])

prop_iia
  :: forall cid pid
  . (Eq cid, Enum cid, Hashable cid, Bounded cid)
  => (HashSet cid -> [Identified "voter" pid (UrBallot "candidate" cid)] -> [HashSet cid])
  -> [Identified "voter" pid (CompleteUrBallot "candidate" cid)]
  -> Bool
prop_iia system (fmap (over value unCompleteBallot) -> ballots) =
  all
    (\candidates ->
      pruneResults candidates (system candidates ballots) ==
      (system candidates (pruneBallots candidates <$> ballots))
    )
    candidateSets
    where
      pruneResults :: HashSet cid -> [HashSet cid] -> [HashSet cid]
      pruneResults candidates = filter (not . Set.null) . map (`Set.intersection` candidates)
      pruneBallots
        :: HashSet cid
        -> Identified "voter" pid (UrBallot "candidate" cid)
        -> Identified "voter" pid (UrBallot "candidate" cid)
      pruneBallots candidates = over value (Set.filter (\ic -> view identifier ic `Set.member` candidates))
      candidateSets :: [HashSet cid]
      candidateSets = fmap Set.fromList . nonEmptyPowerset $ enumFromTo minBound maxBound

-- TODO: This property sometimes throw spurious failures due to ties. We need to handle ties better generally.
prop_pareto
  :: forall cid pid
  . (Eq cid, Bounded cid, Enum cid, Hashable cid, Show cid)
  => (HashSet cid -> [Identified "voter" pid (UrBallot "candidate" cid)] -> [HashSet cid])
  -> [Identified "voter" pid (CompleteUrBallot "candidate" cid)]
  -> Bool
prop_pareto system (fmap (over value unCompleteBallot) -> ballots) =
  all (uncurry outputReflectsInput) candidatePairs
    where
      candidatePairs :: [(cid, cid)]
      candidatePairs = heterogenousPairs $ enumFromTo minBound maxBound
      outputReflectsInput :: cid -> cid -> Bool
      outputReflectsInput l r =
        case (inputPref `implies`) <$> outputPref of
          Just True -> True
          Just False -> trace (show l <> show r <> show inputPref <> show outputPref) False
          Nothing -> error $ "We asked for candidate not in the ballots " <> show l <> " " <> show r
        where
          inputPref = fromMaybe False $ allPreferTo l r (view value <$> ballots)
          outputPref = preferredToInWelfareFunction l r output
          output = system (Set.fromList [l, r]) ballots

implies :: Bool -> Bool -> Bool
implies False _ = True
implies True True = True
implies True False = False


-- TODO: We shouldn't collapse all the failure cases here to `Nothing`.
-- In particular, failure to find a candidate and an empty list of ballots are quite distinct
-- from there being no unified preference.
allPreferTo
  :: (Traversable t, Eq a, Hashable a)
  => a -> a -> t (UrBallot "candidate" a) -> Maybe Bool
allPreferTo l r ballots = do
  prefs <- traverse (preferredToInUrBallot l r) ballots
  let
    -- This a slightly strange contortion that allows us to work with any @Traversable t@, even empty.
    aggregatePref = Set.fromList . Foldable.toList $ prefs
  case Set.size aggregatePref `compare` 1 of
    LT -> Monad.mzero
    GT -> Monad.mzero
    EQ -> pure . List.head . Foldable.toList $ aggregatePref

preferredToInUrBallot :: (Eq a, Hashable a) => a -> a -> UrBallot "candidate" a -> Maybe Bool
preferredToInUrBallot l r ballot =
  (>=) <$> l `Map.lookup` prefMap <*> r `Map.lookup` prefMap
    where
      prefMap = Map.fromList . fmap (\i -> (view identifier i, view value i)) . Foldable.toList $ ballot

heterogenousPairs :: (Eq a) => [a] -> [(a, a)]
heterogenousPairs = filter (uncurry (/=)) . pairs

pairs :: [a] -> [(a, a)]
pairs xs = (,) <$> xs <*> xs

preferredToInWelfareFunction :: (Eq a, Hashable a) => a -> a -> [HashSet a] -> Maybe Bool
preferredToInWelfareFunction l r xs =
  (<=) <$> List.findIndex (l `Set.member`) xs <*> List.findIndex (r `Set.member`) xs

instance (Arbitrary b, Arbitrary c) => Arbitrary (Identified a b c) where
  arbitrary = I <$> arbitrary <*> arbitrary

instance (Arbitrary a, Eq a, Hashable a) => Arbitrary (HashSet a) where
  arbitrary = Set.fromList <$> arbitrary

instance Arbitrary Candidate where
  arbitrary = arbitraryBoundedEnum

instance
  (Bounded a, Enum a, Eq a, Eq b, Hashable a, Hashable b, Arbitrary b) =>
  Arbitrary (CompleteBallot HashSet f b a) where
  arbitrary =
    fromJust . mkCompleteBallot . Set.fromList . zipWith I choices <$> vector (length choices)
      where
        choices :: [a]
        choices = enumFromTo minBound maxBound

x :: IO Result
x = quickCheckResult . prop_iia $ plurality @Candidate @String

y :: IO Result
y = quickCheckResult . prop_pareto $ plurality @Candidate @String



identity :: Iso (Identity a) (Identity b) a b
identity = iso runIdentity Identity

