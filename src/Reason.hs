{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Reason where

import Property
import System as Y
import Scheme
import MathTransform as MT

import Data.Foldable (toList)
import Data.List (foldl, intercalate)
import Data.Sequence ( Seq, (><), (!?))
import qualified Data.Sequence as S
import Data.HashMap.Strict ( (!) )
import qualified Data.HashMap.Strict as HM
import Control.Lens
import Control.Applicative
import qualified Data.Text as T
import Control.Monad.Trans.State.Lazy
import Data.Aeson
import GHC.Generics
import Debug.Trace

data Assertion a = GAssert Id (Property a) | MAssert (Comparison TagOrNat) deriving (Show)

data Reason a = Given |
                Substitution |
                Reason { _name :: T.Text
                       , _systems :: [System a]} deriving (Show, Generic)
makeLenses ''Reason
instance (ToJSON a) => ToJSON (Reason a)
instance (FromJSON a) => FromJSON (Reason a)

assertEq :: Eq a => Assertion a -> Assertion a -> Bool
assertEq (MAssert c1) (MAssert (Compare e1 pt e2)) =
  any (wildCompareEq c1) $ Compare <$> (MT.transform standardRules e1) <*> (pure pt) <*> (MT.transform standardRules e2)
assertEq (GAssert a (Concretely x)) (GAssert b (Concretely y)) = (b == a) && (x == y)
assertEq (GAssert a (Relation pa ra sa)) (GAssert b (Relation pb rb sb)) =
  (a == b) && (pa == pb) && (ra =~= rb) && (sa =~~= sb)
assertEq _ _ = False

wildCompareEq :: Comparison TagOrNat -> Comparison TagOrNat -> Bool
wildCompareEq (Compare ea1 pta ea2) (Compare eb1 ptb eb2) =
  (pta == ptb) && (wildExprEq ea1 eb1) && (wildExprEq ea2 eb2) && (eqMap ea1 eb1 == eqMap ea2 eb2)

wildExprEq :: Expr TagOrNat -> Expr TagOrNat -> Bool
wildExprEq a b = (allButWildEq a b) && (testWilds (eqMap a b) a b)
  where testWilds m (Atom (Nat a)) (Atom (Nat b)) = a == b
        testWilds m (Atom (Tag a)) be@(Atom (Tag b)) = if a < 0 then (m ! a) == be else a == b
        testWilds m (Atom (Tag a)) be = (a < 0) && ((m ! a) == be)
        testWilds m (Negate a) (Negate b) = testWilds m a b
        testWilds m (Add a b) (Add c d) = (testWilds m a c) && (testWilds m b d)
        testWilds m (Sub a b) (Sub c d) = (testWilds m a c) && (testWilds m b d)
        testWilds m (Mult a b) (Mult c d) = (testWilds m a c) && (testWilds m b d)

eqMap :: Expr TagOrNat -> Expr TagOrNat -> HM.HashMap Id (Expr TagOrNat)
eqMap (Atom (Nat a)) (Atom (Nat b)) = HM.empty
eqMap (Atom (Tag a)) b = if a < 0 then HM.singleton a b else HM.empty
eqMap (Negate a) (Negate b) = eqMap a b
eqMap (Add a b) (Add c d) = HM.union (eqMap a c) (eqMap b d)
eqMap (Sub a b) (Sub c d) = HM.union (eqMap a c) (eqMap b d)
eqMap (Mult a b) (Mult c d) = HM.union (eqMap a c) (eqMap b d)
  
allButWildEq :: Expr TagOrNat -> Expr TagOrNat -> Bool
allButWildEq (Atom (Nat a)) (Atom (Nat b)) = a == b
allButWildEq (Atom (Tag a)) (Atom (Tag b)) = (a < 0) || (a == b)
allButWildEq (Atom (Tag a)) be = (a < 0)
allButWildEq (Negate a) (Negate b) = allButWildEq a b
allButWildEq (Add a b) (Add c d) = (allButWildEq a c) && (allButWildEq b d)
allButWildEq (Sub a b) (Sub c d) = (allButWildEq a c) && (allButWildEq b d)
allButWildEq (Mult a b) (Mult c d) = (allButWildEq a c) && (allButWildEq b d)
allButWildEq _ _ = False

implications :: System a -> Seq (Assertion a)
implications s = (foldr (><) S.empty $ objimps <$> (s ^. objs)) >< compimps
  where objimps o = (GAssert (o ^. ident)) <$> (S.filter (isImplication.ptype) $ o ^. props)
        compimps = (fmap MAssert) $ S.fromList $ filter (\(Compare _ pt _) -> isImplication pt) (s ^. Y.comps)

mapAssertion :: MappingPair -> Assertion a -> Assertion a
mapAssertion (im, _) (GAssert i (Relation pt j s)) = GAssert (im ! i) (Relation pt ((im!) <$> j) ((im!) <$> s))
mapAssertion (im, _) (GAssert i c) = GAssert (im ! i) c
mapAssertion m (MAssert (Compare e1 p e2)) = MAssert $ Compare (mapExpression m e1) p (mapExpression m e2)

mapExpression :: MappingPair -> Expr TagOrNat -> Expr TagOrNat
mapExpression m@(im, em) e = if HM.member e em then (em ! e) else
  case e of {
    Atom (Nat a) -> Atom (Nat a);
    Atom (Tag a) -> Atom (Tag (-1-a));
    Negate e1 -> Negate (mapExpression m e1);
    Add e1 e2 -> Add (mapExpression m e1) (mapExpression m e2);
    Mult e1 e2 -> Mult (mapExpression m e1) (mapExpression m e2);
    Sub e1 e2 -> Sub (mapExpression m e1) (mapExpression m e2);
  }

mapImply :: MappingPair -> Assertion a -> Assertion a
mapImply m (GAssert i (Relation (Implies pt) j s)) = mapAssertion m (GAssert i (Relation pt j s))
mapImply m (MAssert (Compare e1 (Implies pt) e2)) = mapAssertion m (MAssert $ Compare e1 pt e2)
mapImply m p = mapAssertion m p

isSubstitution :: System a -> Comparison TagOrNat -> Bool
isSubstitution s c = any (wildCompareEq c) subbed
    where subbed = concat $ applysub <$> (s ^. comps)
          applysub (Compare a pt b) = Compare <$> (MT.transform subrules a) <*> (pure pt) <*> (MT.transform subrules b)
          subrules = go (s ^. comps)
          go ((Compare a Equals b):xs) = toTrans ExactReplace (a, b) : toTrans ExactReplace (b, a) : go xs
          go (x:xs) = go xs
          go _ = []

validateOne :: Eq a => System a -> Assertion a -> Scheme a ()
validateOne r a = StateT $ \s ->
  if any goodmap (systemMatch r s) then
    case a of {
      (GAssert i prop) -> Just ((), addProperty i prop s);
      (MAssert comp) -> Just ((), insertComp comp s);
    }
  else Nothing
  where goodmap m = any (flip assertEq a) $ toList $ (mapImply m) <$> implications r

validate :: Eq a => Reason a -> Assertion a -> Scheme a ()
validate Given a = StateT $ \s ->
  case a of {
      (GAssert i prop) -> Just ((), addProperty i prop s);
      (MAssert comp) -> Just ((), insertComp comp s);
  }
validate Substitution (MAssert c) = StateT $ \s -> 
  if isSubstitution s c then Just ((), insertComp c s) else Nothing
validate r@(Reason _ _) a = StateT $ go (r ^. systems) a
  where go (rr:rrs) a s = (runStateT (validateOne rr a) s) <|> (go rrs a s)
        go _ a s = Nothing

compsFrom :: Seq (Assertion a) -> [Comparison TagOrNat]
compsFrom as = go (toList as)
  where go ((MAssert c):xs) = c : (go xs)
        go (_:xs) = go xs
        go _ = []

-- Testing --

e0 = Add (Atom (Nat 0)) (Atom (Tag 1))
e1 = (Atom (Tag 1))