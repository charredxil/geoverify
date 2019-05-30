{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}

module Property where

import GHC.Generics
import Data.Hashable
import Data.Foldable (toList)
import Data.Aeson

type Id = Int

data Geom = Point
          | Line
          | Segment
          | Ray
          | Circle
          | Angle
          | Value
          | Polygon
          deriving (Show, Eq, Enum, Generic)

instance ToJSON Geom
instance FromJSON Geom
instance Semigroup Geom where
  (<>) a b = a
instance Monoid Geom where
  mempty = Point
instance Hashable Geom where
  hashWithSalt salt g = hashWithSalt salt (fromEnum g)

data PType = Length
           | Radius
           | Degree
           | Equals
           | Congruent
           | Contains
           | Bounded
           | IsRight
           | Similar
           | Implies PType
           | Not PType
           deriving (Show, Eq, Generic)
instance ToJSON PType
instance FromJSON PType

isImplication :: PType -> Bool
isImplication (Implies pt') = True
isImplication _ = False

data Spec r = Spec (Ref r) (Ref r)
  deriving (Eq, Show, Generic)
data Ref r = None | Ref r | Cyc [r] | Ord [r]
  deriving (Eq, Generic)

instance (ToJSON r) => ToJSON (Spec r)
instance (FromJSON r) => FromJSON (Spec r)
instance (ToJSON r) => ToJSON (Ref r)
instance (FromJSON r) => FromJSON (Ref r)
instance Show a => Show (Ref a) where
  show None = ""
  show (Ref a) = show a
  show (Cyc a) = "<" ++ show a ++ ">"
  show (Ord a) = show a
instance Functor Spec where
  fmap f (Spec a b) = Spec (f <$> a) (f <$> b)
instance Functor Ref where
  fmap f None = None
  fmap f (Ref r) = Ref $ f r
  fmap f (Cyc as) = Cyc $ f <$> as
  fmap f (Ord as) = Ord $ f <$> as
instance Foldable Ref where
  foldMap f None = mempty
  foldMap f (Ref r) = f r
  foldMap f (Cyc as) = foldMap f as
  foldMap f (Ord as) = foldMap f as
  foldr f b None = b
  foldr f b (Ref a) = f a b
  foldr f b (Cyc as) = foldr f b as
  foldr f b (Ord as) = foldr f b as
instance Traversable Ref where
  traverse f None = pure None
  traverse f (Ref r) = Ref <$> f r
  traverse f (Cyc as) = Cyc <$> (traverse f as)
  traverse f (Ord as) = Ord <$> (traverse f as)
  --traverse :: Applicative f => (a -> f b) -> t a -> f (t b)

data Expr a = Atom a |
  Add (Expr a) (Expr a) |
  Mult (Expr a) (Expr a) |
  Sub (Expr a) (Expr a) |
  Negate (Expr a)
  deriving (Eq, Show, Generic)
instance (Hashable a) => Hashable (Expr a)
instance (ToJSON a) => ToJSON (Expr a)
instance (FromJSON a) => FromJSON (Expr a)

instance Functor Expr where
  fmap f (Atom a) = Atom $ f a
  fmap f (Add e1 e2) = Add (f <$> e1) (f <$> e2)
  fmap f (Mult e1 e2) = Mult (f <$> e1) (f <$> e2)
  fmap f (Sub e1 e2) = Sub (f <$> e1) (f <$> e2)
  fmap f (Negate e1) = Negate (f <$> e1)
instance Foldable Expr where
  foldMap f (Atom a) = f a
  foldMap f (Negate e) = foldMap f e
  foldMap f (Add e1 e2) = mappend (foldMap f e1) (foldMap f e2)
  foldMap f (Mult e1 e2) = mappend (foldMap f e1) (foldMap f e2)
  foldMap f (Sub e1 e2) = mappend (foldMap f e1) (foldMap f e2)
  foldr f acc (Atom a) = f a acc
  foldr f acc (Negate e) = foldr f acc e
  foldr f acc (Add e1 e2) = foldr f (foldr f acc e1) e2
  foldr f acc (Mult e1 e2) = foldr f (foldr f acc e1) e2
  foldr f acc (Sub e1 e2) = foldr f (foldr f acc e1) e2
instance Traversable Expr where
  traverse f (Atom a) = Atom <$> f a
  traverse f (Negate e) = Negate <$> traverse f e
  traverse f (Add e1 e2) = Add <$> traverse f e1 <*> traverse f e2
  traverse f (Mult e1 e2) = Mult <$> traverse f e1 <*> traverse f e2
  traverse f (Sub e1 e2) = Sub <$> traverse f e1 <*> traverse f e2

data TagOrNat = Tag Id | Nat Integer deriving (Show, Eq, Generic)
instance ToJSON TagOrNat
instance FromJSON TagOrNat
instance Hashable TagOrNat

data Comparison a =  Compare (Expr a) PType (Expr a) deriving (Eq, Show, Generic)
instance (ToJSON a) => ToJSON (Comparison a)
instance (FromJSON a) => FromJSON (Comparison a)

swap :: Spec r -> Spec r
swap (Spec a b) = Spec b a

(=~=) :: Eq r => (Ref r) -> (Ref r) -> Bool
(Cyc as) =~= (Cyc bs) = elem as $ cycPermute bs
_  =~= None = True
ra =~= rb = ra == rb

(=~~=) :: Eq r => (Spec r) -> (Spec r) -> Bool
Spec (Cyc as) (Cyc bs) =~~= Spec (Cyc cs) (Cyc ds) =
  elem (cs, ds) $ zip (cycPermute as) (cycPermute bs)
Spec a b =~~= Spec c d = (a =~= c) && (b =~= d)

cycPermute :: [a] -> [[a]]
cycPermute as = (uniPermutes as) ++ (uniPermutes $ reverse as)
  where takeDrop as t d = take t $ drop d as
        uniPermutes as = takeDrop (cycle as) (length as) <$> [0..(length as - 1)]

cycStandard :: Ord a => [a] -> [a]
cycStandard [a] = [a]
cycStandard xs  = if last mf < (mf !! 1) then (head mf) : (reverse $ tail mf) else mf
  where mf = take (length xs) $ dropWhile (/= (minimum xs)) $ cycle xs

data PropertyG r a = Concretely a
                   | Relation { ptype :: PType, ref :: (Ref r), spec :: (Spec r)}
                   deriving (Eq, Generic)
instance (ToJSON r, ToJSON a) => ToJSON (PropertyG r a)
instance (FromJSON r, FromJSON a) => FromJSON (PropertyG r a)

instance (Show a, Show r) => Show (PropertyG r a) where
  show (Concretely a) = "Concretely " ++ (show a)
  show (Relation pt r _) = (show pt) ++ " " ++ (show r)

type Property a = PropertyG Id a

mkRel :: PType -> r -> PropertyG r a
mkRel pt r = Relation pt (Ref r) (Spec None None)

mkRelR :: PType -> Ref r -> PropertyG r a
mkRelR pt r = Relation pt r (Spec None None)

mkRelN :: PType -> PropertyG r a
mkRelN pt = Relation pt None (Spec None None)

inconcrete :: PropertyG r a -> Bool
inconcrete (Concretely a) = False
inconcrete _ = True

antiparallelPTypes :: PType -> [PType]
antiparallelPTypes Congruent = [Congruent]
antiparallelPTypes Similar = [Similar]
antiparallelPTypes Equals = [Equals]
antiparallelPTypes (Not pt) = Not <$> antiparallelPTypes pt
antiparallelPTypes (Implies pt) = Implies <$> antiparallelPTypes pt
antiparallelPTypes _ = []

parallelPTypes :: PType -> [PType]
parallelPTypes Bounded = [Contains]
parallelPTypes (Not pt) = Not <$> parallelPTypes pt
parallelPTypes (Implies pt) = Implies <$> parallelPTypes pt
parallelPTypes _ = []

additionalProps :: (r, PropertyG r a) -> [(r, PropertyG r a)]
additionalProps (i, Relation pt rr s) = para ++ anti
  where para = (\r pt -> (i, Relation pt (Ref r) s)) <$> (toList rr) <*> (parallelPTypes pt)
        anti = (\r pt -> (r, Relation pt (Ref i) (swap s))) <$> (toList rr) <*> (antiparallelPTypes pt)
additionalProps _ = []
