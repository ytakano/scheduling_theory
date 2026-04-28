{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified JitteredPeriodicEDFSchedulability as EDF

import Control.Monad (forM)
import Crypto.Hash (Digest, SHA256, hash)
import Data.Aeson
  ( FromJSON (parseJSON)
  , Value
  , encode
  , eitherDecodeFileStrict'
  , object
  , withObject
  , (.=)
  , (.:)
  )
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import Data.Char (isSpace, toLower)
import Data.List (isPrefixOf)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Read (readMaybe)

data ParsedTask = ParsedTask
  { parsedCost :: Int
  , parsedPeriod :: Int
  , parsedDeadline :: Int
  , parsedOffset :: Int
  , parsedJitter :: Int
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
  { dbfCutoffJson :: Int
  , dbfBasisJson :: [BasisRowJson]
  , dbfAllBasisCheckedJson :: Bool
  }

data BasisRowJson = BasisRowJson
  { basisT2Json :: Int
  , basisLeftEdgesJson :: [Int]
  }

instance FromJSON Witness where
  parseJSON =
    withObject "Witness" $ \o ->
      Witness
        <$> o .: "schema_version"
        <*> o .: "policy"
        <*> o .: "domain"
        <*> o .: "task_hash"
        <*> o .: "cert"

instance FromJSON CertJson where
  parseJSON =
    withObject "cert" $ \o ->
      CertJson
        <$> o .: "dbf"

instance FromJSON DbfJson where
  parseJSON =
    withObject "dbf" $ \o ->
      DbfJson
        <$> o .: "cutoff"
        <*> o .: "basis"
        <*> o .: "all_basis_checked"

instance FromJSON BasisRowJson where
  parseJSON =
    withObject "basis row" $ \o ->
      BasisRowJson
        <$> o .: "t2"
        <*> o .: "left_edges"

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
  putStrLn "usage: jittered_edf_witness_check --tasks TASKS.csv --witness WITNESS.json"
  putStrLn "       jittered_edf_witness_check --tasks TASKS.csv --emit-expected-witness WITNESS.json"

runCheck :: FilePath -> FilePath -> IO ()
runCheck taskPath witnessPath = do
  taskContent <- readFile taskPath
  case parseCsv taskContent of
    Left err -> reject ("invalid CSV: " ++ err)
    Right tasks -> do
      decoded <- eitherDecodeFileStrict' witnessPath :: IO (Either String Witness)
      case decoded of
        Left err -> reject ("malformed JSON: " ++ err)
        Right witness ->
          case validateWitnessMetadata tasks witness of
            Left err -> reject err
            Right () ->
              case checkWitness tasks witness of
                Left err -> reject err
                Right EDF.True -> putStrLn "ACCEPT" >> exitSuccess
                Right EDF.False -> reject "extracted checker rejected witness"

emitExpectedWitness :: FilePath -> FilePath -> IO ()
emitExpectedWitness taskPath witnessPath = do
  taskContent <- readFile taskPath
  case parseCsv taskContent of
    Left err -> reject ("invalid CSV: " ++ err)
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          cutoff =
            fromNat (EDF.jittered_edf_compact_dbf_certificate_expected_cutoff input)
          basis =
            map fromEDFBasisRow
              (fromEDFList (EDF.jittered_edf_compact_dbf_certificate_expected_basis input))
          dbfObject =
            object
              [ "cutoff" .= cutoff
              , "basis" .= basis
              , "all_basis_checked" .= True
              ]
          witness =
            object
              [ "schema_version" .= (3 :: Int)
              , "policy" .= ("jittered-periodic-edf" :: String)
              , "domain" .= ("uniprocessor" :: String)
              , "task_hash" .= taskHash tasks
              , "cert" .= object
                  [ "dbf" .= dbfObject ]
              ]
      LBS.writeFile witnessPath (encode witness)

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

checkWitness :: [ParsedTask] -> Witness -> Either String EDF.Bool
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

parsePositive :: Int -> String -> String -> Either String Int
parsePositive lineNo name text =
  case readMaybe text of
    Just n | n > 0 -> Right n
    Just _ -> Left ("line " ++ show lineNo ++ ": " ++ name ++ " must be positive")
    Nothing -> Left ("line " ++ show lineNo ++ ": invalid " ++ name ++ ": " ++ text)

parseNonnegative :: Int -> String -> String -> Either String Int
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

checkedNat :: String -> Int -> Either String EDF.Nat
checkedNat label n
  | n >= 0 = Right (toNat n)
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

toNat :: Int -> EDF.Nat
toNat n
  | n <= 0 = EDF.O
  | otherwise = EDF.S (toNat (n - 1))

fromNat :: EDF.Nat -> Int
fromNat EDF.O = 0
fromNat (EDF.S n) = 1 + fromNat n

toEDFBool :: Bool -> EDF.Bool
toEDFBool True = EDF.True
toEDFBool False = EDF.False

fromEDFBasisRow :: EDF.Prod EDF.Time (EDF.List EDF.Time) -> Value
fromEDFBasisRow (EDF.Pair t2 leftEdges) =
  object
    [ "t2" .= fromNat t2
    , "left_edges" .= map fromNat (fromEDFList leftEdges)
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
