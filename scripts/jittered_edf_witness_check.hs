{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified JitteredPeriodicEDFSchedulability as EDF

import CborWitness
import Control.Monad (forM)
import Crypto.Hash (Digest, SHA256, hash)
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace, toLower)
import Data.List (isPrefixOf)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Read (readMaybe)

data ParsedTask = ParsedTask
  { parsedCost :: Integer
  , parsedPeriod :: Integer
  , parsedDeadline :: Integer
  , parsedOffset :: Integer
  , parsedJitter :: Integer
  }
  deriving (Eq, Show)

data Witness = Witness
  { witnessSchemaVersion :: Int
  , witnessPolicy :: String
  , witnessDomain :: String
  , witnessTaskHash :: String
  , witnessCert :: CertJson
  }

newtype CertJson = CertJson
  { certDbf :: DbfJson
  }

data DbfJson = DbfJson
  { dbfCutoffJson :: Integer
  , dbfBasisJson :: [BasisRowJson]
  , dbfAllBasisCheckedJson :: Bool
  }

data BasisRowJson = BasisRowJson
  { basisT2Json :: Integer
  , basisLeftEdgesJson :: [Integer]
  }

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--tasks", taskPath, "--witness", witnessPath] ->
      runCheck taskPath witnessPath
    ["--tasks", taskPath, "--emit-expected-witness", witnessPath] ->
      emitExpectedWitness taskPath witnessPath
    _ -> printUsage >> exitFailure

printUsage :: IO ()
printUsage = do
  putStrLn "usage: jittered_edf_witness_check --tasks TASKS.csv --witness WITNESS.cbor"
  putStrLn "       jittered_edf_witness_check --tasks TASKS.csv --emit-expected-witness WITNESS.cbor"

runCheck :: FilePath -> FilePath -> IO ()
runCheck taskPath witnessPath = do
  taskContent <- readFile taskPath
  case parseCsv taskContent of
    Left err -> reject ("invalid CSV: " ++ err)
    Right tasks -> do
      decoded <- readCborTermFile witnessPath
      case decoded of
        Left err -> reject ("malformed CBOR: " ++ err)
        Right term ->
          case witnessFromTerm term of
            Left err -> reject ("malformed CBOR: " ++ err)
            Right witness -> case validateWitnessMetadata tasks witness of
              Left err -> reject err
              Right () ->
                case checkWitness tasks witness of
                  Left err -> reject err
                  Right True -> putStrLn "ACCEPT" >> exitSuccess
                  Right False -> reject "extracted checker rejected witness"

emitExpectedWitness :: FilePath -> FilePath -> IO ()
emitExpectedWitness taskPath witnessPath = do
  taskContent <- readFile taskPath
  case parseCsv taskContent of
    Left err -> reject ("invalid CSV: " ++ err)
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
      case buildExpectedWitness tasks input of
        Left err -> reject err
        Right witness -> writeCborTermFile witnessPath witness

buildExpectedWitness :: [ParsedTask] -> EDF.List EDF.ExtractedJitteredPeriodicTask -> Either String Term
buildExpectedWitness tasks input = do
  cutoff <-
    checkedNatInteger
      "expected dbf.cutoff"
      (EDF.jittered_edf_compact_dbf_certificate_expected_cutoff input)
  basis <-
    traverse fromEDFBasisRow
      (fromEDFList (EDF.jittered_edf_compact_dbf_certificate_expected_basis input))
  let dbfObject =
        objectTerm
          [ ("cutoff", integerTerm cutoff)
          , ("basis", TList basis)
          , ("all_basis_checked", TBool True)
          ]
  pure $
    objectTerm
      [ ("schema_version", integerTerm 3)
      , ("policy", textTerm "jittered-periodic-edf")
      , ("domain", textTerm "uniprocessor")
      , ("task_hash", textTerm (taskHash tasks))
      , ("cert", objectTerm
          [ ("dbf", dbfObject) ])
      ]

reject :: String -> IO ()
reject err = do
  putStrLn ("REJECT: " ++ err)
  exitFailure

validateWitnessMetadata :: [ParsedTask] -> Witness -> Either String ()
validateWitnessMetadata tasks witness
  | witnessSchemaVersion witness /= 3 =
      Left "unsupported schema_version"
  | witnessPolicy witness /= "jittered-periodic-edf" =
      Left "unsupported policy"
  | witnessDomain witness /= "uniprocessor" =
      Left "unsupported domain"
  | witnessTaskHash witness /= taskHash tasks =
      Left "task_hash mismatch"
  | otherwise = Right ()

witnessFromTerm :: Term -> Either String Witness
witnessFromTerm term = do
  fields <- expectMap "witness" term
  Witness
    <$> intField "witness" "schema_version" fields
    <*> textField "witness" "policy" fields
    <*> textField "witness" "domain" fields
    <*> textField "witness" "task_hash" fields
    <*> (lookupKey "witness" "cert" fields >>= certFromTerm)

certFromTerm :: Term -> Either String CertJson
certFromTerm term = do
  fields <- expectMap "cert" term
  CertJson <$> (lookupKey "cert" "dbf" fields >>= dbfFromTerm)

dbfFromTerm :: Term -> Either String DbfJson
dbfFromTerm term = do
  fields <- expectMap "dbf" term
  DbfJson
    <$> integerField "dbf" "cutoff" fields
    <*> termListField "dbf" "basis" basisRowFromTerm fields
    <*> boolField "dbf" "all_basis_checked" fields

basisRowFromTerm :: Term -> Either String BasisRowJson
basisRowFromTerm term = do
  fields <- expectMap "basis row" term
  BasisRowJson
    <$> integerField "basis row" "t2" fields
    <*> integerListField "basis row" "left_edges" fields

textField :: String -> String -> [(Term, Term)] -> Either String String
textField label key fields =
  lookupKey label key fields >>= expectText (label ++ "." ++ key)

integerField :: String -> String -> [(Term, Term)] -> Either String Integer
integerField label key fields =
  lookupKey label key fields >>= expectInteger (label ++ "." ++ key)

boolField :: String -> String -> [(Term, Term)] -> Either String Bool
boolField label key fields =
  lookupKey label key fields >>= expectBool (label ++ "." ++ key)

intField :: String -> String -> [(Term, Term)] -> Either String Int
intField label key fields = do
  value <- integerField label key fields
  if value >= fromIntegral (minBound :: Int) && value <= fromIntegral (maxBound :: Int)
    then Right (fromInteger value)
    else Left (label ++ "." ++ key ++ " is out of Int range")

termListField :: String -> String -> (Term -> Either String a) -> [(Term, Term)] -> Either String [a]
termListField label key parse fields = do
  value <- lookupKey label key fields
  terms <- expectList (label ++ "." ++ key) value
  traverse parse terms

integerListField :: String -> String -> [(Term, Term)] -> Either String [Integer]
integerListField label key =
  termListField label key (expectInteger (label ++ "." ++ key ++ "[]"))

checkWitness :: [ParsedTask] -> Witness -> Either String Bool
checkWitness tasks witness =
  let input = toEDFList (map toEDFTask tasks)
      dbf = certDbf (witnessCert witness)
  in case witnessSchemaVersion witness of
       3 ->
         EDF.check_jittered_edf_compact_dbf_certificate_extracted input <$> buildDbf dbf
       _ -> Left "unsupported schema_version"

buildDbf :: DbfJson -> Either String EDF.JitteredEDFCompactDbfCertificate
buildDbf dbf =
  EDF.Build_JitteredEDFCompactDbfCertificate
    <$> checkedNat "cert.dbf.cutoff" (dbfCutoffJson dbf)
    <*> checkedBasisRows "cert.dbf.basis" (dbfBasisJson dbf)
    <*> pure (toEDFBool (dbfAllBasisCheckedJson dbf))

parseCsv :: String -> Either String [ParsedTask]
parseCsv content =
  let rows = filter usefulLine (zip [1 :: Int ..] (lines content))
  in case rows of
       [] -> Left "empty CSV: expected at least one task row"
       _ ->
         let rows' = dropHeaderIfPresent rows
         in if null rows'
              then Left "CSV contains a header but no task rows"
              else forM rows' parseTaskRow

usefulLine :: (Int, String) -> Bool
usefulLine (_, line) =
  let s = trim line
  in not (null s) && not ("#" `isPrefixOf` s)

dropHeaderIfPresent :: [(Int, String)] -> [(Int, String)]
dropHeaderIfPresent rows@((_, line) : rest)
  | isHeader line = rest
  | otherwise = rows
dropHeaderIfPresent [] = []

isHeader :: String -> Bool
isHeader line =
  let cells = map normalizeHeaderCell (splitComma line)
  in cells == ["cost", "period", "deadline", "offset", "jitter"]
       || cells == ["cost", "period", "deadline", "offset", "release_jitter"]

normalizeHeaderCell :: String -> String
normalizeHeaderCell =
  map normalizeChar . trim
  where
    normalizeChar c
      | isSpace c = '_'
      | c == '-' = '_'
      | otherwise = toLower c

parseTaskRow :: (Int, String) -> Either String ParsedTask
parseTaskRow (lineNo, line) =
  case map trim (splitComma line) of
    [costText, periodText, deadlineText, offsetText, jitterText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      offset <- parseNonnegative lineNo "offset" offsetText
      jitter <- parseNonnegative lineNo "jitter" jitterText
      pure (ParsedTask cost period deadline offset jitter)
    cols ->
      Left $
        "line " ++ show lineNo ++ ": expected 5 columns, got "
          ++ show (length cols)

parsePositive :: Int -> String -> String -> Either String Integer
parsePositive lineNo name text =
  case readMaybe text of
    Just n | n > 0 -> Right n
    Just _ -> Left ("line " ++ show lineNo ++ ": " ++ name ++ " must be positive")
    Nothing -> Left ("line " ++ show lineNo ++ ": invalid " ++ name ++ ": " ++ text)

parseNonnegative :: Int -> String -> String -> Either String Integer
parseNonnegative lineNo name text =
  case readMaybe text of
    Just n | n >= 0 -> Right n
    Just _ -> Left ("line " ++ show lineNo ++ ": " ++ name ++ " must be nonnegative")
    Nothing -> Left ("line " ++ show lineNo ++ ": invalid " ++ name ++ ": " ++ text)

taskHash :: [ParsedTask] -> String
taskHash tasks =
  "sha256:" ++ show digest
  where
    digest :: Digest SHA256
    digest = hash (BS.pack (canonicalTaskText tasks))

canonicalTaskText :: [ParsedTask] -> String
canonicalTaskText tasks =
  unlines $
    ["schema=jittered-periodic-edf-tasks-v2", "cost,period,deadline,offset,jitter"]
      ++ map renderTask tasks
  where
    renderTask task =
      show (parsedCost task)
        ++ "," ++ show (parsedPeriod task)
        ++ "," ++ show (parsedDeadline task)
        ++ "," ++ show (parsedOffset task)
        ++ "," ++ show (parsedJitter task)

toEDFTask :: ParsedTask -> EDF.ExtractedJitteredPeriodicTask
toEDFTask task =
  EDF.MkExtractedJitteredPeriodicTask
    (toNat (parsedCost task))
    (toNat (parsedPeriod task))
    (toNat (parsedDeadline task))
    (toNat (parsedOffset task))
    (toNat (parsedJitter task))

checkedNat :: String -> Integer -> Either String Integer
checkedNat label n
  | n >= 0 = Right n
  | otherwise = Left (label ++ " must be nonnegative")

checkedNatInteger :: String -> Integer -> Either String Integer
checkedNatInteger label n
  | n >= 0 = Right n
  | otherwise = Left (label ++ " must be nonnegative")

checkedBasisRows :: String -> [BasisRowJson] -> Either String (EDF.List (EDF.Prod EDF.Time (EDF.List EDF.Time)))
checkedBasisRows label rows =
  toEDFList <$> traverse checkedBasisRow rows
  where
    checkedBasisRow row =
      EDF.Pair
        <$> checkedNat (label ++ "[].t2") (basisT2Json row)
        <*> (toEDFList <$> traverse (checkedNat (label ++ "[].left_edges[]")) (basisLeftEdgesJson row))

toEDFList :: [a] -> EDF.List a
toEDFList =
  foldr EDF.Cons EDF.Nil

fromEDFList :: EDF.List a -> [a]
fromEDFList EDF.Nil = []
fromEDFList (EDF.Cons x xs) = x : fromEDFList xs

toNat :: Integer -> Integer
toNat n = n

toEDFBool :: Bool -> Bool
toEDFBool = id

fromEDFBasisRow :: EDF.Prod EDF.Time (EDF.List EDF.Time) -> Either String Term
fromEDFBasisRow (EDF.Pair t2 leftEdges) = do
  t2Json <- checkedNatInteger "expected basis[].t2" t2
  leftEdgesJson <- traverse (checkedNatInteger "expected basis[].left_edges[]") (fromEDFList leftEdges)
  pure $
    objectTerm
      [ ("t2", integerTerm t2Json)
      , ("left_edges", TList (map integerTerm leftEdgesJson))
      ]

trim :: String -> String
trim =
  dropWhile isSpace . reverse . dropWhile isSpace . reverse

splitComma :: String -> [String]
splitComma [] = [""]
splitComma (',' : xs) = "" : splitComma xs
splitComma (x : xs) =
  case splitComma xs of
    [] -> [[x]]
    y : ys -> (x : y) : ys
