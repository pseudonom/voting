{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Voting where

import Control.Lens
import qualified Data.Foldable as Foldable
import Data.Function (on)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import qualified Data.List as List
import GHC.Generics (Generic)
import Numeric.Natural (Natural)

type Ballot f t b a = f (Identified t a b)
type UrBallot t a = Ballot HashSet t Rational a

data Identified t a b
  = I
  { _identifier :: a
  , _value :: b
  } deriving (Show, Eq, Generic, Hashable)
makeLenses ''Identified

-- | Ballots should be exhaustive and non-repetitive
checkCompleteBallot :: forall f a b. (Foldable f, Eq a, Enum a, Bounded a) => f (Identified "candidate" a b) -> Bool
checkCompleteBallot as
  | uniqSize == size && uniqSize == cardinality = True
  | otherwise = False
    where
      uniqSize = Foldable.length . List.nubBy ((==) `on` view identifier) . Foldable.toList $ as
      size = Foldable.length as
      cardinality = Foldable.length (enumFromTo minBound maxBound :: [a])



type PollingRule g c = forall a. UrBallot "candidate" a -> g (Identified "candidate" a c)
type RankVote g = PollingRule g ()

type AggregationRule pid g b h =
  forall cid. (Eq cid, Hashable cid) => [Identified "voter" pid (g (Identified "candidate" cid b))] -> h cid
type RankAggregationRule pid g b h = AggregationRule pid [] () h
type SocialWelfareFunction pid g b = AggregationRule pid g b []
type SocialChoiceFunction pid g b = AggregationRule pid g b Identity
type AnonymousAggregationRule g b h = forall pid. AggregationRule pid g b h
type AnonymousSocialWelfareFunction g b = forall pid. AggregationRule pid g b []
type AnonymousRankSocialWelfareFunction g = forall pid. AggregationRule pid g () []



pluralityPoll :: RankVote Identity
pluralityPoll prefs = Identity $ Foldable.maximumBy (compare `on` view value) prefs & value .~ ()

pluralityAggregate :: AnonymousRankSocialWelfareFunction Identity
pluralityAggregate ballots =
  fmap (view identifier . fst) . reverse . toAscOccurList . toCountMap $ view (value . identity) <$> ballots

toCountMap :: (Eq a, Hashable a) => [a] -> HashMap a Natural
toCountMap = Map.fromListWith (+) . map (\a -> (a, 1))

toAscOccurList :: HashMap a Natural -> [(a, Natural)]
toAscOccurList = List.sortOn snd . Map.toList

plurality :: (Eq cid, Hashable cid) => [Identified "voter" pid (UrBallot "candidate" cid)] -> [cid]
plurality = pluralityAggregate . fmap (over value pluralityPoll)



data Candidates = Alice | Bob | Eve deriving (Bounded, Enum, Eq, Generic, Hashable, Show)

voter1, voter2, voter3 :: Identified "voter" String (UrBallot "candidate" Candidates)
voter1 = I "voter1" . Set.fromList $ [I Alice 1, I Bob 3, I Eve 4]
voter2 = I "voter2" . Set.fromList $ [I Alice 1, I Bob 0, I Eve 0]
voter3 = I "voter3" . Set.fromList $ [I Alice 0, I Bob 0, I Eve 1]

votes :: [Identified "voter" String (UrBallot "candidate" Candidates)]
votes = [voter1, voter2, voter3]




identity :: Iso (Identity a) (Identity b) a b
identity = iso runIdentity Identity

