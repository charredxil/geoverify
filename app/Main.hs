{-# LANGUAGE OverloadedStrings #-}

module Main where

import Lib
import Data.Aeson
import qualified Data.Text as T
import qualified Data.ByteString.Lazy as B
import Control.Monad (join)
import Data.Maybe (fromJust, isJust)
import System.Environment

import Reason
import Proof
import Scheme (buildScheme)
import BaseReasons (baseReasons)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [_] -> error "Too few arguments"
    ("base":fileOut:_) -> base fileOut
    ("verify":fileIn:fileOut:_) -> verify fileIn fileOut
    ("theorize":fileIn:fileOut:_) -> theorize fileIn fileOut
    ("postulate":fileIn:fileOut:_) -> postulate fileIn fileOut
    _ -> error "Invalid arguments"

base :: FilePath -> IO ()
base fileOut = B.writeFile fileOut $ encode (baseReasons :: [Reason Double])

verify :: FilePath -> FilePath -> IO ()
verify fileIn fileOut = do
  proof <- decode <$> (B.readFile fileIn) :: IO (Maybe (Proof Double))
  print proof
  let result = join $ (buildScheme.prove) <$> proof
  B.writeFile fileOut $ encode result

theorize :: FilePath -> FilePath -> IO ()
theorize fileIn fileOut = do
  mtup <- decode <$> (B.readFile fileIn) :: IO (Maybe (T.Text, [Proof Double]))
  let result = join $ (uncurry proveReason) <$> mtup
  B.writeFile fileOut $ encode result

postulate :: FilePath -> FilePath -> IO ()
postulate fileIn fileOut = do
  mtup <- decode <$> (B.readFile fileIn) :: IO (Maybe (T.Text, [[Statement]]))
  let result = (uncurry mkReason) <$> mtup
  B.writeFile fileOut $ encode (result :: Maybe (Reason Double))
