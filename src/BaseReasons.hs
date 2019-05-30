{-# LANGUAGE OverloadedStrings #-}

module BaseReasons where

import Control.Monad.Trans.State.Lazy

import Reason hiding (name)
import Property
import Proof
import System as Y
import Inparse
import Scheme

baseReasons :: Eq a => [Reason a]
baseReasons = [ Given
              , Substitution
              -- TODO get this to work with the web interface
              , rightAngles
              , sideAngleSide
              , reflexive
              , transative
              , symmetric
              , addPOE
              , subPOE
              , multPOE ]

rightAngles :: Reason a
rightAngles = Reason "Right angles are congruent" [buildSchemeUnsafe $ do
    modify $ insertWithProps Angle [mkRelN IsRight]
    modify $ insertWithProps Angle [mkRelN IsRight]
    modify $ addProperty 0 $ mkRel (Implies Congruent) 1
  ]

transative :: Reason a
transative = Reason "Transative Property" [buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 0)) Equals (Atom (Tag 1)))
    modify $ insertComp (Compare (Atom (Tag 1)) Equals (Atom (Tag 2)))
    modify $ insertComp (Compare (Atom (Tag 0)) (Implies Equals) (Atom (Tag 2)))
    modify $ insertComp (Compare (Atom (Tag 2)) (Implies Equals) (Atom (Tag 0)))
  ]

symmetric :: Reason a
symmetric = Reason "Symmetric Property" [buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 0)) Equals (Atom (Tag 1)))
    modify $ insertComp (Compare (Atom (Tag 1)) (Implies Equals) (Atom (Tag 0)))
  ]

addPOE :: Reason a
addPOE = Reason "Addition Property of Equality" [buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 1)) Equals (Atom (Tag 0)))
    modify $ insertComp (Compare (Add (Atom (Tag 1)) (Atom (Tag 2))) (Implies Equals) (Add (Atom (Tag 0)) (Atom (Tag 2))))
  ]

subPOE :: Reason a
subPOE = Reason "Subtraction Property of Equality" [buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 1)) Equals (Atom (Tag 0)))
    modify $ insertComp (Compare (Sub (Atom (Tag 1)) (Atom (Tag 2))) (Implies Equals) (Sub (Atom (Tag 0)) (Atom (Tag 2))))
  ]

multPOE :: Reason a
multPOE = Reason "Multiplication Property of Equality" [buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 1)) Equals (Atom (Tag 0)))
    modify $ insertComp (Compare (Mult (Atom (Tag 1)) (Atom (Tag 2))) (Implies Equals) (Mult (Atom (Tag 0)) (Atom (Tag 2))))
  , buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 1)) Equals (Atom (Tag 0)))
    modify $ insertComp (Compare (Mult (Atom (Tag 2)) (Atom (Tag 1))) (Implies Equals) (Mult (Atom (Tag 2)) (Atom (Tag 0))))
  ]

sideAngleSide :: Eq a => Reason a
sideAngleSide = mkReason "SAS Postulate" [
  [ "–AB ≅ –DE"
  , "–BC ≅ –EF"
  , "∠ABC ≅ ∠DEF"
  , "ΔABC implies ≅ ΔDEF"
  ]]

reflexive :: Eq a => Reason a
reflexive = Reason "Reflexive Property" $ (buildSchemeUnsafe $ do
    modify $ insertComp (Compare (Atom (Tag 0)) (Implies Equals) (Atom (Tag 0)))
  ) : (go <$> enumFrom (toEnum 0 :: Geom)) 
  where go g = buildSchemeUnsafe $ do {
    modify $ insert g;
    modify $ addProperty 0 $ mkRel (Implies Congruent) 0;
  }

-- Testing --
testProof1 :: Eq a => Maybe (Reason a)
testProof1 = proveReason "TEST"
  [[ (Given, "–AB ≅ –BD")
  , (Given, "∠ABC ≅ ∠DBC")
  , (reflexive, "–BC is congruent to –BC")
  , (sideAngleSide, "ΔABC ≅ ΔDBC")
  ]]

testProof2 :: Eq a => Maybe (System a)
testProof2 = buildScheme $ prove
  [ (Given, "AB = BD")
  , (Given, "BD = EA")
  , (transative, "EA = AB")
  , (multPOE, "3*EA = 3*AB")
  ]

testProof3 :: Eq a => Maybe (System a)
testProof3 = buildScheme $ prove [ (Given, "AB = BD")
  , (Given, "BD = EA")
  , (reflexive, "EX = EX")
  ]

testSystem = buildSchemeUnsafe $ do
  modify $ insertComp (Compare (Atom (Tag 0)) (Implies Equals) (Atom (Tag 0)))

testProof4 :: Eq a => Maybe (System a)
testProof4 = buildScheme $ prove 
  [
    (Given, "AB = CD"),
    (Given, "2*CD = RS - 2"),
    (addPOE, "2*CD + 2 = RS - 2 + 2"),
    (Substitution, "2*( AB + 1 ) = RS")
  ]

testProof5 :: Eq a => Maybe (System a)
testProof5 = buildScheme $ prove 
  [
    (Given, "AB = CD"),
    (Given, "2*CD = RS - 2*XY"),
    (addPOE, "2*CD + 2*XY = RS - 2*XY + 2*XY"),
    (Substitution, "2*( AB + XY ) = RS")
  ]