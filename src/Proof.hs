{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Proof where

import Scheme
import System as Y
import qualified System as Y
import Reason hiding (name)
import Property
import Inparse

import qualified Data.Text as T
import Data.Maybe (fromJust, isJust)
import Data.Either.Combinators (rightToMaybe)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Lazy

type Statement = T.Text

type Proof a = [(Reason a, Statement)]

prove :: Eq a => Proof a -> Scheme a ()
prove p = sequence_ $ (uncurry proveBy) <$> p

proveBy :: Eq a => Reason a -> Statement -> Scheme a ()
proveBy r statement = do
  line <- lift $ rightToMaybe $ regularParse proofLine $ T.unpack statement
  proveLineBy r line
  
proveLineBy :: Eq a => Reason a -> Line -> Scheme a ()
proveLineBy r (GLine (Number _) p mc2) = StateT $ \s -> Nothing
proveLineBy r (GLine c1 p (Just (Number _))) = StateT $ \s -> Nothing
proveLineBy r (GLine c1 p mc2) = do
  i1 <- seizeClueId c1
  info1 <- traverse seizeName (textref c1)
  let mi2 = seizeClueId <$> mc2
  ref <- if isJust mi2 then Ref <$> (fromJust mi2) else return None
  info2 <- if isJust mc2 then traverse seizeName (textref $ fromJust mc2) else return None
  validate r (GAssert i1 (Relation p ref $ Spec info1 info2))
proveLineBy r (MLine (Compare e1 p e2)) = do
  ide1 <- traverse seizeClue e1
  ide2 <- traverse seizeClue e2
  validate r (MAssert $ Compare ide1 p ide2)

seizeClueId :: Eq a => Clue -> Scheme a Id
seizeClueId (Number a) = undefined
seizeClueId c = seize (mgetprop c) (mgeom c) (name c)

seizeClue :: Eq a => Clue -> Scheme a TagOrNat
seizeClue (Number a) = return $ Nat a
seizeClue c = Tag <$> (seize (mgetprop c) (mgeom c) (name c))

mkReason :: Eq a => T.Text -> [[Statement]] -> Reason a
mkReason name slists = Reason name systems
  where systems = (buildSchemeUnsafe.(mapM $ proveBy Given)) <$> slists

proveReason :: Eq a => T.Text -> [Proof a] -> Maybe (Reason a)
proveReason name proofs = if valid
  then Just $ mkReason name $ implyLast <$> slists
  else Nothing
  where valid = all (isJust.buildScheme.prove) proofs
        slists = (fmap.fmap) snd proofs
        implyLast [a] = ["implies " <> a]
        implyLast (a:as) = a : implyLast as