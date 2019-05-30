{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module Scheme where

import System as Y
import Property

import Control.Lens
import Data.HashMap.Strict as HM
import Data.Sequence as S
import qualified Data.Text as T
import Data.Maybe (catMaybes, fromJust, isJust)
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class (lift)

type Scheme a r = StateT (System a) Maybe r

getSchemeOutput :: Scheme a r -> (Maybe r)
getSchemeOutput = flip evalStateT Y.empty

buildScheme :: Scheme a r -> Maybe (System a)
buildScheme = flip execStateT Y.empty

buildSchemeUnsafe :: Scheme a r -> System a
buildSchemeUnsafe = (.) fromJust $ flip execStateT Y.empty

retrieveUnsafe :: Eq a => Maybe PType -> Maybe Geom -> Name -> System a -> Id
retrieveUnsafe mpt mg n s = head (retrieveAll mpt mg n s)

retrieve :: Eq a => Maybe PType -> Maybe Geom -> Name -> Scheme a Id
retrieve mpt mg n = do
  s <- get
  let l = retrieveAll mpt mg n s
  if Prelude.null l then lift Nothing
  else return $ head l

retrieveG :: Eq a => Geom -> Name -> Scheme a Id
retrieveG g = retrieve Nothing (Just g)

retrieveAll :: Eq a => Maybe PType -> Maybe Geom -> Name -> System a -> [Id]
retrieveAll mpt (Just g) n s = catMaybes $ (maybeGetProp mpt s) <$> (simple : general ++ specific)
  where chars    = T.singleton <$> (T.unpack n)
        idList   = traverse (flip HM.lookup $ s ^. nameId) $ chars
        refs     = catMaybes [(Cyc . cycStandard) <$> idList, Ord <$> idList, Ref <$> (HM.lookup n $ s ^. nameId)]
        simple   = HM.lookup n (s ^. nameId)
        general  = (flip HM.lookup $ (s ^. referencedBy)) <$> (g,) <$> refs
        specific = case g of {
          Ray   -> if T.length n /= 2 then []
            else [(tuple2 <$> idList) >>= \tp -> (uncurry lookupRay) tp s];
          Angle -> if T.length n /= 3 then []
            else [(tuple3 <$> idList) >>= \tp -> (uncurry3 lookupAngle) tp s];
          _     -> [];
        }
retrieveAll mpt Nothing n s = catMaybes $ (maybeGetProp mpt s) <$> [HM.lookup n (s ^. nameId)]

maybeGetProp :: Maybe PType -> System a -> Maybe Id -> Maybe Id
maybeGetProp Nothing _ mi = mi
maybeGetProp (Just pt) s mi = do
  i <- mi
  o <- S.lookup i (s ^. objs)
  p <- lookupFirstProperty pt o
  case p of Relation _ (Ref r) _ -> return r
            _ -> Nothing

tuple2 [a, b]  = (a, b)
tuple3 [a, b, c]  = (a, b, c)
uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

recentId :: Scheme a Id
recentId = get >>= \s -> return (s ^. nextId - 1)

seizeBasic :: Eq a => Maybe Geom -> Name -> Scheme a Id
seizeBasic mg n = do
  s <- get
  let list = retrieveAll Nothing mg n s
  if not $ Prelude.null list then return $ head list
  else if not $ isJust mg then lift Nothing
  else case g of {
    Point   -> nameit;
    Segment -> if T.length n == 2
      then points >>= \ps -> modify (insertWithProps g $ [mkRelR Bounded $ Cyc ps])
      else nameit;
    Line    -> if T.length n == 2
      then points >>= \ps -> modify (insertWithProps g $ (mkRel Contains) <$> ps)
      else nameit;
    Polygon -> if T.length n >= 3
      then points >>= \ps -> modify (insertWithProps g $ [mkRelR Bounded $ Cyc ps])
      else nameit;
    Ray     -> if T.length n == 2
      then points >>= \[a, b] -> modify (insertWithProps g $ [mkRel Bounded a, mkRel Contains b])
      else nameit;
    Angle   -> if T.length n == 3
      then mapM (seizeG Ray) [T.reverse $ T.take 2 n, T.drop 1 n] >>=
        \[ab, bc] -> modify (insertWithProps g $ [mkRelR Bounded $ Cyc [ab, bc]]);
      else nameit;
  } >> recentId
  where points = mapM (seizeG Point) $ T.singleton <$> T.unpack n
        nameit = modify (insertWithName g n)
        g      = fromJust mg

seize :: Eq a => Maybe (PType, Geom) -> Maybe Geom -> Name -> Scheme a Id
seize Nothing mg n = seizeBasic mg n
seize (Just (pt, fg)) mg n = do
  i <- seizeBasic mg n
  s <- get
  let list = retrieveAll (Just pt) mg n s
  if not $ Prelude.null list then return $ head list
  else do
    fi <- modify (Y.insert fg) >> recentId
    modify (addProperty i $ mkRel pt fi)
    return fi

seizeName :: Eq a => Name -> Scheme a Id
seizeName = seize Nothing Nothing

-- Helper Seize Methods (Semi-useless but good for conciseness and readability) --

seizes :: Eq a => Maybe (PType, Geom) -> Maybe Geom -> [Name] -> Scheme a [Id]
seizes mtup mg ns = mapM (seize mtup mg) ns

seizeG :: Eq a => Geom -> Name -> Scheme a Id
seizeG g = seize Nothing (Just g)

seizesG :: Eq a => Geom -> [Name] -> Scheme a [Id]
seizesG g = seizes Nothing (Just g)

seizeProp :: Eq a => (PType, Geom) -> Maybe Geom -> Name -> Scheme a Id
seizeProp tup = seize (Just tup)

seizesProp :: Eq a => (PType, Geom) -> Maybe Geom -> [Name] -> Scheme a [Id]
seizesProp tup = seizes (Just tup)

seizePropG :: Eq a => (PType, Geom) -> Geom -> Name -> Scheme a Id
seizePropG tup g = seize (Just tup) (Just g)

seizesPropG :: Eq a => (PType, Geom) -> Geom -> [Name] -> Scheme a [Id]
seizesPropG tup g = seizes (Just tup) (Just g)

seizeVal :: Eq a => PType -> Maybe Geom -> Name -> Scheme a Id
seizeVal pt = seize (Just (pt, Value))

seizesVal :: Eq a => PType -> Maybe Geom -> [Name] -> Scheme a [Id]
seizesVal pt = seizes (Just (pt, Value))

seizeValG :: Eq a => PType -> Geom -> Name -> Scheme a Id
seizeValG pt g = seize (Just (pt, Value)) (Just g)

seizesValG :: Eq a => PType -> Geom -> [Name] -> Scheme a [Id]
seizesValG pt g = seizes (Just (pt, Value)) (Just g)
