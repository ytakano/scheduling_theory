{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified PeriodicEDFSchedulability as EDF

import Control.Monad (forM)
import Crypto.Hash (Digest, SHA256, hash)
import Data.Aeson
  ( FromJSON (parseJSON)
  , Value
  , eitherDecodeFileStrict'
  , withObject
  , (.:)
  )
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
  }
  deriving (Eq, Show)

data Witness = Witness
  { witnessSchemaVersion :: Int
  , witnessPolicy :: String
  , witnessDomain :: String
  , witnessTaskHash :: String
  , witnessCert :: CertJson
  , witnessSidecar :: SidecarJson
  }

data CertJson = CertJson
  { certPrefix :: PrefixJson
  , certTransport :: TransportJson
  , certDbf :: DbfJson
  }

data PrefixJson = PrefixJson
  { prefixHorizonJson :: Integer
  , prefixBasisJobsJson :: [Integer]
  , prefixSlotsJson :: [Maybe Integer]
  , prefixCompletedByJson :: [Integer]
  , prefixBacklogFreeMatrixJson :: [[Bool]]
  }

data TransportJson = TransportJson
  { transportPeriodJson :: Integer
  , transportBasisJobsJson :: [Integer]
  , transportClassesJson :: [TransportClassJson]
  , transportJobClassJson :: [Integer]
  , transportJobShiftJson :: [Integer]
  }

data TransportClassJson = TransportClassJson
  { transportRepJobJson :: Integer
  , transportCompletionOffsetJson :: Integer
  , transportBacklogOffsetJson :: Integer
  }

data DbfJson = DbfJson
  { dbfCutoffJson :: Integer
  , dbfOkTableJson :: [Bool]
  }

data SidecarJson = SidecarJson
  { sidecarCandidateJobsJson :: [Integer]
  , sidecarClassRelevantJobsJson :: [[Integer]]
  , sidecarWindowTargetCertsJson :: [WindowTargetCertJson]
  , sidecarPostResetWindowTargetCertsJson :: [WindowTargetCertJson]
  }

data WindowPairCertJson = WindowPairCertJson
  { windowTargetEarlierJobJson :: Integer
  , windowRepEarlierJobJson :: Integer
  , windowTransportDeltaJson :: Integer
  }

data WindowTargetCertJson = WindowTargetCertJson
  { windowTransportTargetJobJson :: Integer
  , windowTransportClassIdJson :: Integer
  , windowTransportShiftJson :: Integer
  , windowTransportPairsJson :: [WindowPairCertJson]
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
        <*> o .: "sidecar"

instance FromJSON CertJson where
  parseJSON =
    withObject "cert" $ \o ->
      CertJson
        <$> o .: "prefix"
        <*> o .: "transport"
        <*> o .: "dbf"

instance FromJSON PrefixJson where
  parseJSON =
    withObject "prefix" $ \o ->
      PrefixJson
        <$> o .: "horizon"
        <*> o .: "basis_jobs"
        <*> o .: "slots"
        <*> o .: "completed_by"
        <*> o .: "backlog_free_matrix"

instance FromJSON TransportJson where
  parseJSON =
    withObject "transport" $ \o ->
      TransportJson
        <$> o .: "period"
        <*> o .: "basis_jobs"
        <*> o .: "classes"
        <*> o .: "job_class"
        <*> o .: "job_shift"

instance FromJSON TransportClassJson where
  parseJSON =
    withObject "transport_class" $ \o ->
      TransportClassJson
        <$> o .: "rep_job"
        <*> o .: "completion_offset"
        <*> o .: "backlog_offset"

instance FromJSON DbfJson where
  parseJSON =
    withObject "dbf" $ \o ->
      DbfJson
        <$> o .: "cutoff"
        <*> o .: "ok_table"

instance FromJSON SidecarJson where
  parseJSON =
    withObject "sidecar" $ \o ->
      SidecarJson
        <$> o .: "candidate_jobs"
        <*> o .: "class_relevant_jobs"
        <*> o .: "window_target_certs"
        <*> o .: "post_reset_window_target_certs"

instance FromJSON WindowPairCertJson where
  parseJSON =
    withObject "window_pair_cert" $ \o ->
      WindowPairCertJson
        <$> o .: "target_earlier_job"
        <*> o .: "rep_earlier_job"
        <*> o .: "delta"

instance FromJSON WindowTargetCertJson where
  parseJSON =
    withObject "window_target_cert" $ \o ->
      WindowTargetCertJson
        <$> o .: "target_job"
        <*> o .: "class_id"
        <*> o .: "shift"
        <*> o .: "pairs"

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--tasks", taskPath, "--witness", witnessPath] ->
      runCheck False taskPath witnessPath
    ["--tasks", taskPath, "--offsets", "--witness", witnessPath] ->
      runCheck True taskPath witnessPath
    ["--offsets", "--tasks", taskPath, "--witness", witnessPath] ->
      runCheck True taskPath witnessPath
    _ -> printUsage >> exitFailure

printUsage :: IO ()
printUsage = do
  putStrLn "usage: periodic_edf_witness_check --tasks TASKS.csv --witness WITNESS.json"
  putStrLn "       periodic_edf_witness_check --tasks TASKS.csv --offsets --witness WITNESS.json"

runCheck :: Bool -> FilePath -> FilePath -> IO ()
runCheck useOffsets taskPath witnessPath = do
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
            Right () -> do
              case buildCheckerInput witness of
                Left err -> reject err
                Right (cert, sidecar) -> do
                  let input = toEDFList (map toEDFTask tasks)
                      accepted =
                        if useOffsets
                          then EDF.check_periodic_edf_checked_sidecar_extracted_with_offsets input cert sidecar
                          else EDF.check_periodic_edf_checked_sidecar_extracted input cert sidecar
                  case accepted of
                    True -> putStrLn "ACCEPT" >> exitSuccess
                    False -> reject "extracted checker rejected witness"

reject :: String -> IO ()
reject err = do
  putStrLn ("REJECT: " ++ err)
  exitFailure

validateWitnessMetadata :: [ParsedTask] -> Witness -> Either String ()
validateWitnessMetadata tasks witness
  | witnessSchemaVersion witness /= 1 =
      Left "unsupported schema_version"
  | witnessPolicy witness /= "periodic-edf" =
      Left "unsupported policy"
  | witnessDomain witness /= "uniprocessor" =
      Left "unsupported domain"
  | witnessTaskHash witness /= taskHash tasks =
      Left "task_hash mismatch"
  | otherwise = Right ()

buildCheckerInput ::
  Witness ->
  Either String (EDF.EDFInfiniteCert EDF.JobId, EDF.PeriodicEDFCheckedSidecarCert)
buildCheckerInput witness = do
  cert <- buildCert (witnessCert witness)
  sidecar <- buildSidecar (witnessSidecar witness)
  pure (cert, sidecar)

buildCert :: CertJson -> Either String (EDF.EDFInfiniteCert EDF.JobId)
buildCert cert =
  EDF.Build_EDFInfiniteCert
    <$> buildPrefix (certPrefix cert)
    <*> buildTransport (certTransport cert)
    <*> buildDbf (certDbf cert)

buildPrefix :: PrefixJson -> Either String (EDF.EDFPrefixCert EDF.JobId)
buildPrefix prefix =
  EDF.Build_EDFPrefixCert
    <$> checkedNat "prefix.horizon" (prefixHorizonJson prefix)
    <*> checkedNatList "prefix.basis_jobs" (prefixBasisJobsJson prefix)
    <*> checkedSlotList "prefix.slots" (prefixSlotsJson prefix)
    <*> checkedNatList "prefix.completed_by" (prefixCompletedByJson prefix)
    <*> checkedBoolRows "prefix.backlog_free_matrix" (prefixBacklogFreeMatrixJson prefix)

buildTransport :: TransportJson -> Either String (EDF.EDFTransportCert EDF.JobId)
buildTransport transport = do
  classes <- traverse buildTransportClass (transportClassesJson transport)
  EDF.Build_EDFTransportCert
    <$> checkedNat "transport.period" (transportPeriodJson transport)
    <*> checkedNatList "transport.basis_jobs" (transportBasisJobsJson transport)
    <*> pure (toEDFList classes)
    <*> checkedNatList "transport.job_class" (transportJobClassJson transport)
    <*> checkedNatList "transport.job_shift" (transportJobShiftJson transport)

buildTransportClass :: TransportClassJson -> Either String (EDF.EDFTransportClass EDF.JobId)
buildTransportClass cls =
  EDF.Build_EDFTransportClass
    <$> checkedNat "transport.classes[].rep_job" (transportRepJobJson cls)
    <*> checkedNat "transport.classes[].completion_offset" (transportCompletionOffsetJson cls)
    <*> checkedNat "transport.classes[].backlog_offset" (transportBacklogOffsetJson cls)

buildDbf :: DbfJson -> Either String EDF.EDFDBFCert
buildDbf dbf =
  EDF.Build_EDFDBFCert
    <$> checkedNat "dbf.cutoff" (dbfCutoffJson dbf)
    <*> checkedBoolList "dbf.ok_table" (dbfOkTableJson dbf)

buildSidecar :: SidecarJson -> Either String EDF.PeriodicEDFCheckedSidecarCert
buildSidecar sidecar = do
  candidateJobs <- checkedNatList "sidecar.candidate_jobs" (sidecarCandidateJobsJson sidecar)
  classRelevantJobs <-
    checkedNatRows "sidecar.class_relevant_jobs" (sidecarClassRelevantJobsJson sidecar)
  windowTargets <-
    traverse buildWindowTarget (sidecarWindowTargetCertsJson sidecar)
  postResetTargets <-
    traverse buildWindowTarget (sidecarPostResetWindowTargetCertsJson sidecar)
  pure $
    EDF.Build_PeriodicEDFCheckedSidecarCert
      candidateJobs
      classRelevantJobs
      (toEDFList windowTargets)
      (toEDFList postResetTargets)

buildWindowTarget :: WindowTargetCertJson -> Either String EDF.EDFWindowTransportTargetCert
buildWindowTarget target = do
  pairs <- traverse buildWindowPair (windowTransportPairsJson target)
  EDF.Build_EDFWindowTransportTargetCert
    <$> checkedNat "window_target.target_job" (windowTransportTargetJobJson target)
    <*> checkedNat "window_target.class_id" (windowTransportClassIdJson target)
    <*> checkedNat "window_target.shift" (windowTransportShiftJson target)
    <*> pure (toEDFList pairs)

buildWindowPair :: WindowPairCertJson -> Either String EDF.EDFWindowTransportPairCert
buildWindowPair pair =
  EDF.Build_EDFWindowTransportPairCert
    <$> checkedNat "window_pair.target_earlier_job" (windowTargetEarlierJobJson pair)
    <*> checkedNat "window_pair.rep_earlier_job" (windowRepEarlierJobJson pair)
    <*> checkedNat "window_pair.delta" (windowTransportDeltaJson pair)

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
  in cells == ["cost", "period", "deadline"]
       || cells == ["cost", "period", "deadline", "offset"]

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
    [costText, periodText, deadlineText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      pure (ParsedTask cost period deadline 0)
    [costText, periodText, deadlineText, offsetText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      offset <- parseNonnegative lineNo "offset" offsetText
      pure (ParsedTask cost period deadline offset)
    cols ->
      Left $
        "line " ++ show lineNo ++ ": expected 3 or 4 columns, got "
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
    ["schema=periodic-edf-tasks-v1", "cost,period,deadline,offset"]
      ++ map renderTask tasks
  where
    renderTask task =
      show (parsedCost task)
        ++ "," ++ show (parsedPeriod task)
        ++ "," ++ show (parsedDeadline task)
        ++ "," ++ show (parsedOffset task)

toEDFTask :: ParsedTask -> EDF.ExtractedPeriodicTask
toEDFTask task =
  EDF.MkExtractedPeriodicTask
    (toNat (parsedCost task))
    (toNat (parsedPeriod task))
    (toNat (parsedDeadline task))
    (toNat (parsedOffset task))

checkedNat :: String -> Integer -> Either String Integer
checkedNat label n
  | n >= 0 = Right n
  | otherwise = Left (label ++ " must be nonnegative")

checkedNatList :: String -> [Integer] -> Either String (EDF.List Integer)
checkedNatList label xs =
  toEDFList <$> traverse (checkedNat label) xs

checkedNatRows :: String -> [[Integer]] -> Either String (EDF.List (EDF.List Integer))
checkedNatRows label rows =
  toEDFList <$> traverse (checkedNatList label) rows

checkedSlotList :: String -> [Maybe Integer] -> Either String (EDF.List (EDF.Option Integer))
checkedSlotList label slots =
  toEDFList <$> traverse checkedSlot slots
  where
    checkedSlot Nothing = Right EDF.None
    checkedSlot (Just n) = EDF.Some <$> checkedNat label n

checkedBoolList :: String -> [Bool] -> Either String (EDF.List Bool)
checkedBoolList _ xs =
  Right (toEDFList (map toEDFBool xs))

checkedBoolRows :: String -> [[Bool]] -> Either String (EDF.List (EDF.List Bool))
checkedBoolRows label rows =
  toEDFList <$> traverse (checkedBoolList label) rows

toEDFList :: [a] -> EDF.List a
toEDFList =
  foldr EDF.Cons EDF.Nil

toNat :: Integer -> Integer
toNat n = n

toEDFBool :: Bool -> Bool
toEDFBool = id

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
