{-# LANGUAGE OverloadedStrings #-}

module MathTransform where 

import Property

import Data.HashMap.Strict ( (!) )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Maybe (catMaybes, isJust, fromJust)
import Debug.Trace

type Transform = (Expr TagOrNat -> [Expr TagOrNat])
type ReplacePair = (Expr TagOrNat, Expr TagOrNat)

genericEq :: Expr TagOrNat -> Expr TagOrNat -> Bool
genericEq a b = (replaceStructEq a b) && (go (replaceEqMap a b) a b)
    where go m (Atom (Tag a)) e = (m ! a) == e
          go m (Negate a) (Negate b) = go m a b
          go m (Add a b) (Add c d) = (go m a c) && (go m b d)
          go m (Sub a b) (Sub c d) = (go m a c) && (go m b d)
          go m (Mult a b) (Mult c d) = (go m a c) && (go m b d)
          go _ _ _ = True

replaceEqMap :: Expr TagOrNat -> Expr TagOrNat -> HM.HashMap Id (Expr TagOrNat)
replaceEqMap (Atom (Nat a)) (Atom (Nat b)) = HM.empty
replaceEqMap (Atom (Tag a)) e = HM.singleton a e
replaceEqMap (Negate a) (Negate b) = replaceEqMap a b
replaceEqMap (Add a b) (Add c d) = HM.union (replaceEqMap a c) (replaceEqMap b d)
replaceEqMap (Sub a b) (Sub c d) = HM.union (replaceEqMap a c) (replaceEqMap b d)
replaceEqMap (Mult a b) (Mult c d) = HM.union (replaceEqMap a c) (replaceEqMap b d)

replaceStructEq :: Expr TagOrNat -> Expr TagOrNat -> Bool
replaceStructEq (Atom (Nat a)) (Atom (Nat b)) = a == b
replaceStructEq (Atom (Tag a)) e = True
replaceStructEq (Negate a) (Negate b) = replaceStructEq a b
replaceStructEq (Add a b) (Add c d) = (replaceStructEq a c) && (replaceStructEq b d)
replaceStructEq (Sub a b) (Sub c d) = (replaceStructEq a c) && (replaceStructEq b d)
replaceStructEq (Mult a b) (Mult c d) = (replaceStructEq a c) && (replaceStructEq b d)
replaceStructEq _ _ = False

data ReplaceType = ExactReplace | MapReplace

fullReplace :: ReplaceType -> Expr TagOrNat -> ReplacePair -> Maybe (Expr TagOrNat)
fullReplace MapReplace e (f, t) = if genericEq f e then Just $ (go (replaceEqMap f e) t) else Nothing
    where go m (Atom (Tag a)) = m ! a
          go m atom@(Atom (Nat a)) = atom
          go m (Negate e) = Negate (go m e)
          go m (Add a b) = Add (go m a) (go m b)
          go m (Mult a b) = Mult (go m a) (go m b)
          go m (Sub a b) = Sub (go m a) (go m b)
fullReplace ExactReplace e (f, t) = if e == f then Just t else Nothing


toTrans ::  ReplaceType -> ReplacePair -> Transform
toTrans rt t e = catMaybes $ (fullReplace rt e t) : (Just <$> (subs e))
    where subs (Negate e) = Negate <$> toTrans rt t e
          subs (Add a b) = (Add <$> toTrans rt t a <*> (pure b)) ++ (Add a <$> toTrans rt t b)
          subs (Mult a b) = (Mult <$> toTrans rt t a <*> (pure b)) ++ (Mult a <$> toTrans rt t b)
          subs (Sub a b) = (Sub <$> toTrans rt t a <*> (pure b)) ++ (Sub a <$> toTrans rt t b)
          subs x = [x]

toMapTrans = toTrans MapReplace

transformOnce :: [Transform] -> Transform
transformOnce tr e = HS.toList $ HS.fromList $ concat (tr <*> (pure e))

transformOnceSet :: [Transform] -> Expr TagOrNat -> HS.HashSet (Expr TagOrNat)
transformOnceSet tr e = HS.fromList $ concat (tr <*> (pure e))

transformAllOnceSet :: [Transform] -> HS.HashSet (Expr TagOrNat) -> HS.HashSet (Expr TagOrNat)
transformAllOnceSet tr s = HS.unions (transformOnceSet tr <$> (HS.toList s))

transform :: [Transform] -> Expr TagOrNat -> [Expr TagOrNat]
transform tr e = HS.toList $ go initial (transformAllOnceSet tr initial) 0
    where initial = HS.singleton e
          go _ s 4 = s
          go p s n = if (length p) == (length s) then p else go s (HS.union s $ transformAllOnceSet tr $ HS.difference s p) (n+1)

-- Rules --

zero = Atom (Nat 0)
one = Atom (Nat 1)
t0 = Atom (Tag 0)
t1 = Atom (Tag 1)
t2 = Atom (Tag 2)

addCommute =  [( Add t1 t2 , Add t2 t1 )]
multCommute = [( Mult t1 t2 , Mult t2 t1 )]
addAssoc =    [( Add (Add t0 t1) t2 , Add t0 (Add t1 t2) )]
multAssoc =   [( Mult (Mult t0 t1) t2 , Mult t0 (Mult t1 t2) )]
addId =       [( Add t1 zero , t1 ), ( Add zero t1 , t1 )]
multId =      [( Mult one t1 , t1 ), ( Mult t1 one , t1 )]
subInverse =  [( Sub t1 t1 , zero )]
addInverse =  [( Add t1 (Negate t1) , zero ), ( Add (Negate t1) t1 , zero )]
distribTwo =  [( Mult t0 (Add t1 t2) ,  Add (Mult t0 t1) (Mult t0 t2) )]
distribId  =  [( Mult t0 (Add t1 one) ,  Add (Mult t0 t1) t0 ), ( Mult t0 (Add one t1) ,  Add t0 (Mult t0 t1) )]

simplify :: Expr TagOrNat -> Maybe Integer
simplify (Add a b) = (+) <$> (simplify a) <*> (simplify b)
simplify (Mult a b) = (*) <$> (simplify a) <*> (simplify b)
simplify (Sub a b) = (-) <$> (simplify a) <*> (simplify b)
simplify (Negate a) = ((-1)*) <$> (simplify a)
simplify (Atom (Tag _)) = Nothing
simplify (Atom (Nat a)) = Just a

simplifyTrans :: Expr TagOrNat -> [Expr TagOrNat]
simplifyTrans e = if isJust mint then (Atom (Nat (fromJust mint))) : (subs e) else (subs e)
    where mint = simplify e
          subs (Negate e) = Negate <$> simplifyTrans e
          subs (Add a b) = (Add <$> simplifyTrans a <*> (simplifyTrans b))
          subs (Mult a b) = (Mult <$> simplifyTrans a <*> (simplifyTrans b))
          subs (Sub a b) = (Mult <$> simplifyTrans a <*> (simplifyTrans b))
          subs x = [x]

standardRules :: [Transform]
standardRules = (++) funclist $ toMapTrans <$> (unreversable ++ rawlist ++ ((\(a, b) -> (b, a)) <$> rawlist))
    where funclist = [ simplifyTrans ]
          rawlist = concat [ addAssoc
                    , multAssoc
                    , distribTwo
                    , distribId
                    ]
          unreversable = concat [ addCommute, multCommute, subInverse, addInverse, addId, multId]

fastRules :: [Transform]
fastRules = (++) funclist $ toMapTrans <$> (unreversable ++ rawlist ++ ((\(a, b) -> (b, a)) <$> rawlist))
    where funclist = [ simplifyTrans ]
          rawlist = concat [ addAssoc, multAssoc, distribTwo, distribId ]
          unreversable = concat [ addInverse, addId, multId ]

-- Testing --

expr0 = Add (Add t1 one) one
expr1 = Add (Add one one) t1
expr2 = Mult (Add (Mult (Atom (Tag 1)) (Atom (Tag 2))) (Mult (Atom (Tag 1)) (Atom (Tag 2)))) (Add (Mult (Atom (Tag 1)) (Atom (Tag 2))) (Mult (Atom (Tag 1)) (Atom (Tag 2))))
    

    