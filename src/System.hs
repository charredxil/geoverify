{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module System where

import Property
import MathTransform as MT

import GHC.Generics
import Control.Lens
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Sequence as S
import Data.List (foldl, intercalate)
import Data.Sequence (Seq ( (:|>) ), empty)
import qualified Data.HashMap.Strict as HM
import qualified Data.IntSet as I
import qualified Data.Tree as Tree
import qualified Data.Text as T
import Control.Monad (join)
import Data.Maybe (catMaybes, isJust)
import Data.Bits (xor)
import Data.Hashable
import Data.Aeson
import Debug.Trace

-- Types and Typeclass Instances

type Name = T.Text

instance Hashable (Ref Id) where
  hashWithSalt s None     = hashWithSalt s s
  hashWithSalt s (Ref x)  = hashWithSalt s x
  hashWithSalt s (Cyc xs) = s `hashWithSalt` (0::Int) `hashWithSalt` xs
  hashWithSalt s (Ord xs) = s `hashWithSalt` (1::Int) `hashWithSalt` xs

data Obj a = Obj { _geom  :: Geom
                 , _ident :: Id
                 , _props :: Seq (Property a) } deriving (Generic)
makeLenses ''Obj
instance (ToJSON a) => ToJSON (Obj a)
instance (FromJSON a) => FromJSON (Obj a)
instance (Show a) => Show (Obj a) where
  show (Obj g i ps) = (show i) ++ ": " ++ (show g) ++ " " ++ (show $ toList ps)

data System a = System { _nextId :: Id
                       , _objs :: Seq (Obj a)
                       , _comps :: [Comparison TagOrNat]
                       , _referencedBy :: HM.HashMap (Geom, Ref Id) Id
                       , _nameId :: HM.HashMap Name Id} deriving (Generic)
makeLenses ''System
instance (ToJSON a) => ToJSON (System a)
instance (FromJSON a) => FromJSON (System a)
instance (Show a) => Show (System a) where
  show s = intercalate "\n" ((toList $ show <$> (s ^. objs)) ++ (show <$> (s ^. comps)))

-- Basic Methods --

newObj :: Geom -> Id -> Obj a
newObj g i = Obj g i S.empty

empty :: System a
empty = System 0 S.empty [] HM.empty HM.empty

insert :: Geom -> System a -> System a
insert g s = (nextId %~ (+1)) $ (objs %~ (:|> (newObj g $ s ^. nextId))) s

insertComp :: Comparison TagOrNat -> System a -> System a
insertComp (Compare e1 pt e2) = comps %~ (inputs ++)
  where inputs = Compare <$> (MT.transform rules e1) <*> (pure pt) <*> (MT.transform rules e2)
        rules = fastRules

addProperty :: Id -> Property a -> System a -> System a
addProperty i p s = foldr addPropertyAlone' s ips
  where ips = (i, p) : (additionalProps (i, p))

addPropertyAlone' :: (Id, Property a) -> System a -> System a
addPropertyAlone' (i, p) s = over (objs.(ix i).props) (:|> p) s'
  where s' = case p of (Relation Bounded r _) -> addReference i r s
                       _  -> s

addPropertyGeom :: Id -> PropertyG Geom a -> System a -> System a
addPropertyGeom i (Relation pt g _) s = (addProperty i p') s'
  where p'  = mkRel pt (s ^. nextId)
        s'  = (compose $ insert <$> toList g) s

insertWithProps :: Geom -> [Property a] -> System a -> System a
insertWithProps g ps s = ((compose $ addProperty i <$> ps).(insert g)) s
  where i = s ^. nextId

insertWithName :: Geom -> Name -> System a -> System a
insertWithName g n s = (nameObj (s ^. nextId) n) $ (insert g) s

nameObj :: Id -> Name -> System a -> System a
nameObj i n = nameId %~ (HM.insert n i)

nameObjs :: [Id] -> [Name] -> System a -> System a
nameObjs is ns = compose $ (uncurry nameObj) <$> (zip is ns)

addReference :: Id -> Ref Id -> System a -> System a
addReference i r s = referencedBy %~ (HM.insert (s ^. (objs.(ix i).geom), r') i) $ s
  where r' = case r of (Cyc xs) -> Cyc $ cycStandard xs
                       _ -> r

-- Insertion Helper Methods --

compose :: [a -> a] -> a -> a
compose = foldr (.) id

lookupProperty :: PType -> Obj a -> Seq (Property a)
lookupProperty pt o = S.filter ((==pt).ptype) $ S.filter inconcrete $ view props o

lookupFirstProperty :: PType -> Obj a -> Maybe (Property a)
lookupFirstProperty pt o = S.lookup 0 $ lookupProperty pt o

lookupRay :: Eq a => Id -> Id -> System a -> Maybe Id
lookupRay a b s = (^. ident) <$> (S.lookup 0 $ S.filter predicate $ s ^. objs)
  where predicate o = (o ^. geom == Ray) &&
                      (isJust $ S.elemIndexL (mkRel Bounded a) $ o ^. props) &&
                      (isJust $ S.elemIndexL (mkRel Contains b) $ o ^. props)

lookupAngle :: Eq a => Id -> Id -> Id -> System a -> Maybe Id
lookupAngle a b c s = do
    rayba <- lookupRay b a s
    raybc <- lookupRay b c s
    HM.lookup (Angle, (Cyc . cycStandard) [rayba, raybc]) (s ^. referencedBy)

insertSegBetween :: Id -> Id -> System a -> System a
insertSegBetween a b s = ((addProperty i $ mkRelR Bounded (Cyc [a, b])).(insert Segment)) s
  where i = s ^. nextId

insertPolygon :: Int -> System a -> System a
insertPolygon n s = ((compose $ (uncurry insertSegBetween) <$> tups).
                    (addProperty i $ mkRelR Bounded $ Cyc [(i+1)..(i+n)]).
                    (compose $ replicate n $ insert Point).
                    (insert Polygon)) s
  where i    = s ^. nextId
        tups = zip [(i+1)..(i+n)] ((i+n) : [(i+1)..(i+n-1)])



-- Matching --

type ExprMapping = HM.HashMap (Expr TagOrNat) (Expr TagOrNat)
type MappingPair = (IdMapping, ExprMapping)
type State a = (System a, System a, MappingPair, [Comparison TagOrNat])

systemMatch :: System a -> System a -> [MappingPair]
systemMatch a b = concat $ (catMaybes . concat . Tree.levels) <$> trees
  where trees = (\im -> Tree.unfoldTree expand (a, b, (im, HM.empty), a ^. comps)) <$> (idSystemMatch a b)

expand :: State a -> (Maybe MappingPair, [State a])
expand (a, b, (im, m), (c:cs)) = (Nothing, (\mm -> (a, b, (im, mm), cs)) <$> maps)
  where maps = catMaybes $ (join.(fmap $ connectWhile linked m).(compMatch im c)) <$> (b ^. comps)
expand (_, _, mm, []) = (Just mm, [])

compMatch :: IdMapping -> Comparison TagOrNat -> Comparison TagOrNat -> Maybe ExprMapping
compMatch im (Compare _ (Implies _) _) _ = Just $ HM.empty
compMatch im (Compare ea1 pta ea2) (Compare eb1 ptb eb2) = if pta /= ptb then Nothing else
  join $ (connectWhile linked) <$> (exprMatch im ea1 eb1) <*> (exprMatch im ea2 eb2)

exprMatch :: IdMapping -> Expr TagOrNat -> Expr TagOrNat -> Maybe ExprMapping
exprMatch im (Atom (Nat a)) (Atom (Nat b)) = if a == b then Just HM.empty else Nothing
exprMatch im ae@(Atom (Tag a)) be@(Atom (Tag b)) = 
  if (HM.member a im) && (im HM.! a) /= b then Nothing else Just $ HM.singleton ae be
exprMatch im ae@(Atom (Tag a)) be = if HM.member a im then Nothing else Just $ HM.singleton ae be
exprMatch im (Negate a) (Negate b) = exprMatch im a b
exprMatch im (Add a1 a2) (Add b1 b2) = join $ (connectWhile linked) <$> em1 <*> em2
  where em1 = exprMatch im a1 b1
        em2 = exprMatch im a2 b2
exprMatch im (Mult a1 a2) (Mult b1 b2) = join $ (connectWhile linked) <$> em1 <*> em2
  where em1 = exprMatch im a1 b1
        em2 = exprMatch im a2 b2
exprMatch _ _ _ = Nothing

type IdMapping = HM.HashMap Id Id
type IdState a = (System a, System a, IdMapping, [Id])

idSystemMatch :: System a -> System a -> [IdMapping]
idSystemMatch a b = (catMaybes . concat . Tree.levels) tree
  where tree = Tree.unfoldTree idExpand (a, b, HM.empty, [0..((a ^. nextId) - 1)])

idExpand :: IdState a -> (Maybe IdMapping, [IdState a])
idExpand (a, b, m, (u:us))
  | HM.member u m = let lobj = (b ^. objs) `S.index` (m HM.! u) in
                    (Nothing, (\m -> (a, b, m, us)) <$> (catMaybes $ connectWhile linked m <$> objectMatch uobj lobj))
  | otherwise     = (Nothing, (\m -> (a, b, m, us)) <$> maps)
  where uobj = (toList $ a ^. objs) !! u
        maps = (concat.toList) $ (catMaybes.(fmap $ connectWhile linked m).(objectMatch uobj)) <$> (b ^. objs)
idExpand (_, _, m, []) = (Just m, [])

linked :: (Hashable a, Eq a) => HM.HashMap a a -> a -> a -> Bool
linked m a b = not $ ((HM.member a m) && ((m HM.! a) /= b))

linkedHarsh :: (Hashable a, Eq a) => HM.HashMap a a -> a -> a -> Bool
linkedHarsh m a b = not $ ((HM.member a m) && ((m HM.! a) /= b)) || ((not $ HM.member a m) && (elem b (HM.elems m)))

connectWhile :: (Hashable a, Eq a) => (HM.HashMap a a -> a -> a -> Bool) -> HM.HashMap a a -> HM.HashMap a a -> Maybe (HM.HashMap a a)
connectWhile f a b = if go (HM.toList a) b then Just (mappend a b) else Nothing
  where go ((x, y):a) b = (f b x y) && (go a b)
        go _ b = True

objectMatch :: Obj a -> Obj a -> [IdMapping]
objectMatch a b
  | a ^. geom /= b ^. geom = []
  | otherwise = HM.insert (a ^. ident) (b ^. ident) <$> (match (toList $ a ^. props) (toList $ b ^. props) HM.empty)
  where match (x:xs) b m
          | isImplication $ ptype x = match xs b m
          | otherwise = concat $ fmap (match xs b) $ concat $ fmap (catMaybes.(fmap $ connectWhile linkedHarsh m).(propertyMatch x)) b
        match _ _ m = [m]

propertyMatch :: Property a -> Property a -> [IdMapping]
propertyMatch (Relation r i spa) (Relation s j spb) = if r /= s then [] else result
  where result = HM.union <$> (refMatch i j) <*> (specMatch spa spb)
propertyMatch _ _ = [HM.empty]

specMatch :: Spec Id -> Spec Id -> [IdMapping]
specMatch (Spec (Cyc a) (Cyc b)) (Spec (Cyc c) (Cyc d)) =
  if (length a == length c) && (length b == length d) then
  fmap (HM.fromList . (zip (c ++ d))) $ zipWith (++) (cycPermute a) (cycPermute b) else []
specMatch (Spec a b) (Spec c d) = HM.union <$> (refMatch a c) <*> (refMatch b d)

refMatch :: Ref Id -> Ref Id -> [IdMapping]
refMatch None _ = [HM.empty]
refMatch (Ref a) (Ref b) = [HM.singleton a b]
refMatch (Ord as) (Ord bs) =
  if length as == length bs then [HM.fromList $ zip as bs] else []
refMatch (Cyc as) (Cyc bs) =
  if length as == length bs then fmap (HM.fromList . (zip as)) $ cycPermute bs else []
refMatch _ _ = []

