{-# LANGUAGE OverloadedStrings #-}

module Inparse where

import Scheme
import System as Y hiding (name, geom, ptype)
import qualified System as Y
import Reason (Assertion)
import Property hiding (ptype, Nat)

import Text.Parsec (parse, ParseError)
import Text.Parsec.Prim (unexpected, try)
import Text.Parsec.String (Parser)
import Text.Parsec.Char (letter, char, digit, string, oneOf)
import Text.Parsec.Combinator (many1, manyTill, eof, choice, anyToken, optionMaybe, notFollowedBy)
import Text.Parsec.Expr
import Text.Parsec.Token hiding (lexeme)
import Text.Parsec.Language (javaStyle)
import Control.Monad (void, guard)
import Control.Applicative ((<$>), (<*>), (<*), (<|>), many, (<$))
import qualified Data.Text as T

data Clue = Clue { mgetprop :: Maybe (PType, Geom)
                 , mgeom :: Maybe Geom
                 , name :: Name
                 , textref :: Ref T.Text } 
            | Number Integer
              deriving (Show)

data Line = GLine Clue PType (Maybe Clue) | MLine (Comparison Clue) deriving (Show)

exClue s = regularParse clue s
exLine s = regularParse proofLine s

replaceSubs :: Comparison a -> Comparison a
replaceSubs (Compare e1 pt e2) = Compare (go e1) pt (go e2)
  where go (Sub a b) = (Add (go a) (Negate (go b)))
        go (Negate a) = Negate (go a)
        go (Atom a) = (Atom a)
        go (Mult a b) = Mult (go a) (go b)
        go (Add a b) = Add (go a) (go b)

proofLine :: Parser Line
proofLine = choice [
  try implyPrefixProofLine,
  genericProofLine
  ]

genericProofLine :: Parser Line
genericProofLine = choice [
    try $ GLine <$> clue <*> geoptype <*> (optionMaybe clue)
  , (MLine . replaceSubs) <$> (Compare <$> expr <*> mathptype <*> expr)
  ]

implyPrefixProofLine :: Parser Line
implyPrefixProofLine = do
  void $ lexeme $ string "implies"
  implyify <$> genericProofLine
  where implyify (GLine a pt b) = GLine a (Implies pt) b
        implyify (MLine (Compare a pt b)) = MLine $ Compare a (Implies pt) b

--TODO add "not" capabilities
geoptype :: Parser PType
geoptype = choice [
  try $ Length <$ parseLength,
  try $ Radius <$ parseRadius,
  try $ Degree <$ parseDegree,
  try $ Congruent <$ parseCongruent,
  try $ Contains <$ parseContains,
  try $ Bounded <$ parseBounded,
  try $ IsRight <$ parseIsRight,
  try $ parseImplies geoptype,
  Similar <$ parseSimilar ]

mathptype :: Parser PType
mathptype = choice [
  try $ Equals <$ parseEquals,
  parseImplies mathptype ]

-- Expression Parsing --

exprLexer = makeTokenParser javaStyle

expr = buildExpressionParser exprTable exprTerm

exprTerm = parens exprLexer expr <|> (Atom <$> clue)

exprTable = [ [prefix "-" Negate, prefix "+" id]
  , [binary "*" Mult AssocLeft]
  , [binary "+" Add AssocLeft, binary "-" Sub AssocLeft]
  ]

binary  name fun assoc = Infix (do{ reservedOp exprLexer name; return fun }) assoc
prefix  name fun       = Prefix (do{ reservedOp exprLexer name; return fun })

-- Clue Parsing --

clue :: Parser Clue
clue = choice [
  try (Number <$> (natural exprLexer)),
  try segLengthClue,
  genericClue ]

segLengthClue :: Parser Clue
segLengthClue = do
  ns <- nameString
  if length ns /= 2
    then do unexpected "expecting a name length of 2"
    else do return $ Clue (Just (Length, Value)) (Just Segment) (T.pack ns) None

genericClue :: Parser Clue
genericClue = do
  p <- propPrefix
  g <- geom
  n <- T.pack <$> nameString
  return $ Clue p g n (makeInfo g n)

makeInfo :: (Maybe Geom) -> T.Text -> Ref T.Text
makeInfo (Just Polygon) n = Cyc $ T.singleton <$> (T.unpack n)
makeInfo _ _ = None

propPrefix :: Parser (Maybe (PType, Geom))
propPrefix = lexeme $ choice [
  Just (Degree, Value) <$ string "m",
  return Nothing ]

geom :: Parser (Maybe Geom)
geom = lexeme $ choice [
  Just Point <$ string ".",
  Just Polygon <$ string "Δ",
  Just Line <$ string "↔️",
  Just Ray <$ string "→",
  Just Segment <$ string "–",
  Just Angle <$ string "∠",
  return Nothing ]

nameString :: Parser String
nameString = lexeme $ many1Till letter (void (oneOf " \t\n") <|> eof)

-- PType Parsers --

parseImplies :: Parser PType -> Parser PType
parseImplies parser = do
  lexeme $ string "implies"
  Implies <$> parser

parseLength :: Parser String
parseLength = lexeme $ string "has length"
parseRadius :: Parser String
parseRadius = lexeme $ string "has radius"
parseDegree :: Parser String
parseDegree = lexeme $ string "has degree"
parseEquals :: Parser String
parseEquals = lexeme $ choice [
  string "=",
  string "is equal to" ]
parseCongruent :: Parser String
parseCongruent = lexeme $ choice [
  string "≅",
  string "is congruent to" ]
parseContains :: Parser String
parseContains = lexeme $ string "contains"
parseBounded :: Parser String
parseBounded = lexeme $ string "is bounded by"
parseIsRight :: Parser String
parseIsRight = lexeme $ string "is " >> choice [
  string "a right angle",
  string "right" ]
parseSimilar :: Parser String
parseSimilar = lexeme $ string "is similar to"

-- Helper Functions --

many1Till :: Show b => Parser a -> Parser b -> Parser [a]
many1Till p end = do
    notFollowedBy end
    p1 <- p
    ps <- manyTill p end
    return (p1:ps)

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

regularParse :: Parser a -> String -> Either ParseError a
regularParse p = parse p ""

parseWithEof :: Parser a -> String -> Either ParseError a
parseWithEof p = parse (p <* eof) ""

parseWithLeftOver :: Parser a -> String -> Either ParseError (a,String)
parseWithLeftOver p = parse ((,) <$> p <*> leftOver) ""
  where leftOver = manyTill anyToken eof
