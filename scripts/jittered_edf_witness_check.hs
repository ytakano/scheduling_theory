{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified JitteredPeriodicEDFSchedulability as EDF

import CborWitness
import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (forM)
import Crypto.Hash (Digest, SHA256, hash)
import qualified Data.ByteString.Char8 as BS
import Data.Char (isSpace, toLower)
import Data.List (isPrefixOf)
import qualified GHC.Clock as Clock
import qualified GHC.Conc as GHC
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Printf (printf)
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

data ThreadSetting
  = ThreadCount Int
  | ThreadAuto
  deriving (Eq, Show)

data CheckOptions = CheckOptions
  { optTasksPath :: FilePath
  , optWitnessPath :: FilePath
  , optThreads :: ThreadSetting
  , optBlockWindows :: Int
  , optMetricsOut :: Maybe FilePath
  }

data Mode
  = WitnessMode CheckOptions
  | EmitExpectedWitnessMode FilePath FilePath

data CheckMetrics = CheckMetrics
  { metricThreads :: Int
  , metricBlockWindows :: Int
  , metricActualRows :: Int
  , metricActualWindows :: Integer
  , metricActualBlocks :: Int
  , metricRangeCount :: Int
  , metricRangeRowsMin :: Int
  , metricRangeRowsMax :: Int
  , metricRangeWindowsMin :: Integer
  , metricRangeWindowsMax :: Integer
  , metricFailedRangeIndex :: Maybe Int
  , metricExpectedRows :: Int
  , metricExpectedWindows :: Integer
  , metricExpectedBlocks :: Int
  , metricResult :: Bool
  , metricPhaseCsvReadSeconds :: Double
  , metricPhaseCsvParseSeconds :: Double
  , metricPhaseCborDecodeSeconds :: Double
  , metricPhaseWitnessDecodeSeconds :: Double
  , metricPhaseMetadataValidateSeconds :: Double
  , metricPhaseBuildDbfSeconds :: Double
  , metricPhaseResolveThreadsSeconds :: Double
  , metricPhaseActualBasisCountSeconds :: Double
  , metricPhaseExpectedBasisGenerateSeconds :: Double
  , metricPhaseRangePlanSeconds :: Double
  , metricPhaseRangeCoverSeconds :: Double
  , metricPhaseRangeEqualitySeconds :: Double
  , metricPhaseRangeNdbfSeconds :: Double
  , metricPhaseActualSplitSeconds :: Double
  , metricPhaseExpectedSplitSeconds :: Double
  , metricPhaseStructuralSeconds :: Double
  , metricPhaseWorkersSeconds :: Double
  , metricPhaseCheckTotalSeconds :: Double
  }

data InputPhaseMetrics = InputPhaseMetrics
  { inputPhaseCsvReadSeconds :: Double
  , inputPhaseCsvParseSeconds :: Double
  , inputPhaseCborDecodeSeconds :: Double
  , inputPhaseWitnessDecodeSeconds :: Double
  , inputPhaseMetadataValidateSeconds :: Double
  , inputPhaseBuildDbfSeconds :: Double
  }

data RangeWorkItem = RangeWorkItem
  { rangeIndex :: Int
  , rangeLo :: EDF.Time
  , rangeHi :: EDF.Time
  , rangeActualBasis :: EDF.JitteredCompactDbfBasis
  }

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left err -> putStrLn err >> printUsage >> exitFailure
    Right (WitnessMode opts) ->
      runCheck opts
    Right (EmitExpectedWitnessMode taskPath witnessPath) ->
      emitExpectedWitness taskPath witnessPath

printUsage :: IO ()
printUsage = do
  putStrLn "usage: jittered_edf_witness_check --tasks TASKS.csv --witness WITNESS.cbor [--threads 1|N|auto] [--block-windows N] [--metrics-out PATH]"
  putStrLn "       jittered_edf_witness_check --tasks TASKS.csv --emit-expected-witness WITNESS.cbor"

parseArgs :: [String] -> Either String Mode
parseArgs args =
  go args Nothing Nothing (ThreadCount 1) 100000 Nothing
  where
    go [] (Just taskPath) (Just (Left witnessPath)) threads blockWindows metricsOut =
      Right (WitnessMode (CheckOptions taskPath witnessPath threads blockWindows metricsOut))
    go [] (Just taskPath) (Just (Right witnessPath)) (ThreadCount 1) 100000 Nothing =
      Right (EmitExpectedWitnessMode taskPath witnessPath)
    go [] _ _ _ _ _ =
      Left "invalid arguments"
    go ("--tasks" : path : rest) Nothing mode threads blockWindows metricsOut =
      go rest (Just path) mode threads blockWindows metricsOut
    go ("--witness" : path : rest) taskPath Nothing threads blockWindows metricsOut =
      go rest taskPath (Just (Left path)) threads blockWindows metricsOut
    go ("--emit-expected-witness" : path : rest) taskPath Nothing threads blockWindows metricsOut =
      go rest taskPath (Just (Right path)) threads blockWindows metricsOut
    go ("--threads" : value : rest) taskPath mode _ blockWindows metricsOut =
      case parseThreads value of
        Left err -> Left err
        Right threads -> go rest taskPath mode threads blockWindows metricsOut
    go ("--block-windows" : value : rest) taskPath mode threads _ metricsOut =
      case readMaybe value of
        Just n | n > 0 -> go rest taskPath mode threads n metricsOut
        _ -> Left "--block-windows must be positive"
    go ("--metrics-out" : path : rest) taskPath mode threads blockWindows Nothing =
      go rest taskPath mode threads blockWindows (Just path)
    go _ _ _ _ _ _ =
      Left "invalid arguments"

parseThreads :: String -> Either String ThreadSetting
parseThreads value
  | map toLower value == "auto" = Right ThreadAuto
  | otherwise =
      case readMaybe value of
        Just n | n > 0 -> Right (ThreadCount n)
        _ -> Left "--threads must be positive or auto"

runCheck :: CheckOptions -> IO ()
runCheck opts = do
  let taskPath = optTasksPath opts
      witnessPath = optWitnessPath opts
  (taskContent, phaseCsvRead) <- timedIO (readFile taskPath)
  (parsedTasks, phaseCsvParse) <- timedEval (parseCsv taskContent)
  case parsedTasks of
    Left err -> reject ("invalid CSV: " ++ err)
    Right tasks -> do
      (decoded, phaseCborDecode) <- timedIO (readCborTermFile witnessPath)
      case decoded of
        Left err -> reject ("malformed CBOR: " ++ err)
        Right term -> do
          (decodedWitness, phaseWitnessDecode) <- timedEval (witnessFromTerm term)
          case decodedWitness of
            Left err -> reject ("malformed CBOR: " ++ err)
            Right witness -> do
              (metadataResult, phaseMetadataValidate) <-
                timedEval (validateWitnessMetadata tasks witness)
              case metadataResult of
                Left err -> reject err
                Right () -> do
                  (dbfResult, phaseBuildDbf) <-
                    timedEval (buildDbf (certDbf (witnessCert witness)))
                  case dbfResult of
                    Left err -> reject err
                    Right cert -> do
                      let input = toEDFList (map toEDFTask tasks)
                          inputPhases =
                            InputPhaseMetrics
                              { inputPhaseCsvReadSeconds = phaseCsvRead
                              , inputPhaseCsvParseSeconds = phaseCsvParse
                              , inputPhaseCborDecodeSeconds = phaseCborDecode
                              , inputPhaseWitnessDecodeSeconds = phaseWitnessDecode
                              , inputPhaseMetadataValidateSeconds = phaseMetadataValidate
                              , inputPhaseBuildDbfSeconds = phaseBuildDbf
                              }
                      (ok, metrics) <- runParallelBlockCheck inputPhases opts input cert
                      writeMetrics (optMetricsOut opts) metrics
                      if ok
                        then putStrLn "ACCEPT" >> exitSuccess
                        else reject "extracted checker rejected witness"

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

runParallelBlockCheck ::
  InputPhaseMetrics ->
  CheckOptions ->
  EDF.List EDF.ExtractedJitteredPeriodicTask ->
  EDF.JitteredEDFCompactDbfCertificate ->
  IO (Bool, CheckMetrics)
runParallelBlockCheck inputPhases opts input cert = do
  checkStart <- monotonicSeconds
  (threads, phaseResolveThreads) <- timedIO (resolveThreads (optThreads opts))
  GHC.setNumCapabilities threads
  let blockWindows = optBlockWindows opts
      actualBasis = EDF.jedf_compact_basis cert
      expectedCutoff = EDF.jittered_edf_compact_dbf_certificate_expected_cutoff input
  ((actualRows, actualWindows), phaseActualBasisCount) <-
    timedEval (basisCounts actualBasis)
  (workItems, phaseRangePlan) <-
    timedIO (forceRangeWorkItems (planRangeWorkItems blockWindows actualBasis))
  let actualRanges = map rangeActualBasis workItems
      rangeList = map rangeTimeRange workItems
      actualRangesList = toEDFList actualRanges
      rangeListEDF = toEDFList rangeList
      rangeStats = rangeMetrics workItems
      headerOk =
        EDF.check_jittered_edf_compact_dbf_certificate_header_extracted input cert
      rangeCoverOk =
        EDF.time_ranges_cover_horizon_b expectedCutoff rangeListEDF
      rangeEqualityOk =
        EDF.compact_dbf_basis_eqb actualBasis (EDF.concat actualRangesList)
      structural = headerOk && rangeCoverOk && rangeEqualityOk
      rangeCount = length workItems
      metrics result failedRange phaseRangeCover phaseRangeEquality phaseStructural phaseWorkers phaseCheckTotal =
        CheckMetrics
          { metricThreads = threads
          , metricBlockWindows = blockWindows
          , metricActualRows = actualRows
          , metricActualWindows = actualWindows
          , metricActualBlocks = rangeCount
          , metricRangeCount = rangeCount
          , metricRangeRowsMin = rangeRowsMin rangeStats
          , metricRangeRowsMax = rangeRowsMax rangeStats
          , metricRangeWindowsMin = rangeWindowsMin rangeStats
          , metricRangeWindowsMax = rangeWindowsMax rangeStats
          , metricFailedRangeIndex = failedRange
          , metricExpectedRows = 0
          , metricExpectedWindows = 0
          , metricExpectedBlocks = 0
          , metricResult = result
          , metricPhaseCsvReadSeconds = inputPhaseCsvReadSeconds inputPhases
          , metricPhaseCsvParseSeconds = inputPhaseCsvParseSeconds inputPhases
          , metricPhaseCborDecodeSeconds = inputPhaseCborDecodeSeconds inputPhases
          , metricPhaseWitnessDecodeSeconds = inputPhaseWitnessDecodeSeconds inputPhases
          , metricPhaseMetadataValidateSeconds = inputPhaseMetadataValidateSeconds inputPhases
          , metricPhaseBuildDbfSeconds = inputPhaseBuildDbfSeconds inputPhases
          , metricPhaseResolveThreadsSeconds = phaseResolveThreads
          , metricPhaseActualBasisCountSeconds = phaseActualBasisCount
          , metricPhaseExpectedBasisGenerateSeconds = 0
          , metricPhaseRangePlanSeconds = phaseRangePlan
          , metricPhaseRangeCoverSeconds = phaseRangeCover
          , metricPhaseRangeEqualitySeconds = phaseRangeEquality
          , metricPhaseRangeNdbfSeconds = phaseWorkers
          , metricPhaseActualSplitSeconds = phaseRangePlan
          , metricPhaseExpectedSplitSeconds = 0
          , metricPhaseStructuralSeconds = phaseStructural
          , metricPhaseWorkersSeconds = phaseWorkers
          , metricPhaseCheckTotalSeconds = phaseCheckTotal
          }
  (rangeCoverResult, phaseRangeCover) <- timedEval rangeCoverOk
  (rangeEqualityResult, phaseRangeEquality) <- timedEval rangeEqualityOk
  (structuralOk, phaseStructural) <- timedEval (headerOk && rangeCoverResult && rangeEqualityResult)
  if not structuralOk
    then do
      checkEnd <- monotonicSeconds
      pure (False, metrics False Nothing phaseRangeCover phaseRangeEquality phaseStructural 0 (checkEnd - checkStart))
    else do
      (failedRange, phaseWorkers) <-
        timedIO $
          parallelRangeChecks threads $
            map (checkRange input) workItems
      let ok = structuralOk && failedRange == Nothing
      checkEnd <- monotonicSeconds
      pure (ok, metrics ok failedRange phaseRangeCover phaseRangeEquality phaseStructural phaseWorkers (checkEnd - checkStart))

timedEval :: a -> IO (a, Double)
timedEval value =
  timedIO (evaluate value)

timedIO :: IO a -> IO (a, Double)
timedIO action = do
  start <- monotonicSeconds
  value <- action
  end <- monotonicSeconds
  pure (value, end - start)

monotonicSeconds :: IO Double
monotonicSeconds = do
  nanoseconds <- Clock.getMonotonicTimeNSec
  pure (fromIntegral nanoseconds / 1000000000.0)

resolveThreads :: ThreadSetting -> IO Int
resolveThreads (ThreadCount n) = pure n
resolveThreads ThreadAuto = max 1 <$> GHC.getNumProcessors

checkRange :: EDF.List EDF.ExtractedJitteredPeriodicTask -> RangeWorkItem -> (Int, Bool)
checkRange input item =
  ( rangeIndex item
  , EDF.check_jittered_edf_compact_dbf_certificate_range_extracted
      input
      (rangeLo item)
      (rangeHi item)
      (rangeActualBasis item)
  )

parallelAll :: Int -> [Bool] -> IO Bool
parallelAll _ [] = pure True
parallelAll threads checks
  | threads <= 1 = go checks
  | otherwise = do
      let chunks = splitIntoAtMost threads checks
      vars <- forM chunks $ \chunk -> do
        var <- newEmptyMVar
        _ <- forkIO $ do
          result <- try (evaluate (and chunk)) :: IO (Either SomeException Bool)
          putMVar var result
        pure var
      results <- mapM takeMVar vars
      case sequence results of
        Left _ -> pure False
        Right oks -> pure (and oks)
  where
    go [] = pure True
    go (x : xs) = do
      ok <- evaluate x
      if ok then go xs else pure False

splitIntoAtMost :: Int -> [a] -> [[a]]
splitIntoAtMost n xs =
  filter (not . null) (go n xs)
  where
    go parts rest
      | parts <= 1 = [rest]
      | null rest = []
      | otherwise =
          let takeCount = (length rest + parts - 1) `div` parts
              (chunk, remaining) = splitAt takeCount rest
          in chunk : go (parts - 1) remaining

parallelRangeChecks :: Int -> [(Int, Bool)] -> IO (Maybe Int)
parallelRangeChecks _ [] = pure Nothing
parallelRangeChecks threads checks
  | threads <= 1 = go checks
  | otherwise = do
      let chunks = splitIntoAtMost threads checks
      vars <- forM chunks $ \chunk -> do
        var <- newEmptyMVar
        _ <- forkIO $ do
          result <- try (evaluate (firstFailedRange chunk)) :: IO (Either SomeException (Maybe Int))
          putMVar var result
        pure var
      results <- mapM takeMVar vars
      case sequence results of
        Left _ -> pure (Just 0)
        Right failures -> pure (minimumMaybe failures)
  where
    go [] = pure Nothing
    go ((idx, ok) : xs) = do
      result <- evaluate ok
      if result then go xs else pure (Just idx)

firstFailedRange :: [(Int, Bool)] -> Maybe Int
firstFailedRange [] = Nothing
firstFailedRange ((idx, ok) : xs)
  | ok = firstFailedRange xs
  | otherwise = Just idx

minimumMaybe :: [Maybe Int] -> Maybe Int
minimumMaybe values =
  case [idx | Just idx <- values] of
    [] -> Nothing
    idxs -> Just (minimum idxs)

splitBasisByWindows :: Int -> EDF.JitteredCompactDbfBasis -> [EDF.JitteredCompactDbfBasis]
splitBasisByWindows limit basis =
  map toEDFList (splitRows [] 0 (fromEDFList basis))
  where
    splitRows [] _ [] = []
    splitRows current _ [] = [reverse current]
    splitRows [] _ (row : rows) =
      splitRows [row] (rowWindowCount row) rows
    splitRows current currentWeight (row : rows)
      | currentWeight >= fromIntegral limit =
          reverse current : splitRows [row] (rowWindowCount row) rows
      | currentWeight + rowWindowCount row > fromIntegral limit =
          reverse current : splitRows [row] (rowWindowCount row) rows
      | otherwise =
          splitRows (row : current) (currentWeight + rowWindowCount row) rows

planRangeWorkItems :: Int -> EDF.JitteredCompactDbfBasis -> [RangeWorkItem]
planRangeWorkItems limit basis =
  zipWith mkRangeWorkItem [0 :: Int ..] (splitRows [] 0 (fromEDFList basis))
  where
    splitRows [] _ [] = []
    splitRows current _ [] = [reverse current]
    splitRows [] _ (row : rows) =
      splitRows [row] (rowWindowCount row) rows
    splitRows current currentWeight (row : rows)
      | currentWeight >= fromIntegral limit =
          reverse current : splitRows [row] (rowWindowCount row) rows
      | currentWeight + rowWindowCount row > fromIntegral limit =
          reverse current : splitRows [row] (rowWindowCount row) rows
      | otherwise =
          splitRows (row : current) (currentWeight + rowWindowCount row) rows

mkRangeWorkItem :: Int -> [EDF.Prod EDF.Time (EDF.List EDF.Time)] -> RangeWorkItem
mkRangeWorkItem idx [] =
  error ("empty range work item: " ++ show idx)
mkRangeWorkItem idx rows@(firstRow : _) =
  RangeWorkItem
    { rangeIndex = idx
    , rangeLo = rowT2 firstRow
    , rangeHi = lastRowT2 rows + 1
    , rangeActualBasis = toEDFList rows
    }

rangeTimeRange :: RangeWorkItem -> EDF.TimeRange
rangeTimeRange item =
  EDF.MkTimeRange (rangeLo item) (rangeHi item)

rowT2 :: EDF.Prod EDF.Time (EDF.List EDF.Time) -> EDF.Time
rowT2 (EDF.Pair t2 _) = t2

lastRowT2 :: [EDF.Prod EDF.Time (EDF.List EDF.Time)] -> EDF.Time
lastRowT2 [] =
  error "empty range work item"
lastRowT2 [row] = rowT2 row
lastRowT2 (_ : rows) = lastRowT2 rows

basisRowCount :: EDF.JitteredCompactDbfBasis -> Int
basisRowCount =
  length . fromEDFList

basisWindowCount :: EDF.JitteredCompactDbfBasis -> Integer
basisWindowCount =
  sum . map rowWindowCount . fromEDFList

basisCounts :: EDF.JitteredCompactDbfBasis -> (Int, Integer)
basisCounts basis =
  let rows = fromEDFList basis
      rowCount = length rows
      windowCount = sum (map rowWindowCount rows)
  in rowCount `seq` windowCount `seq` (rowCount, windowCount)

forceBlockList :: [EDF.JitteredCompactDbfBasis] -> IO [EDF.JitteredCompactDbfBasis]
forceBlockList blocks = do
  _ <- evaluate (length blocks)
  pure blocks

forceRangeWorkItems :: [RangeWorkItem] -> IO [RangeWorkItem]
forceRangeWorkItems items = do
  _ <- evaluate (length items)
  pure items

rowWindowCount :: EDF.Prod EDF.Time (EDF.List EDF.Time) -> Integer
rowWindowCount (EDF.Pair _ leftEdges) =
  fromIntegral (length (fromEDFList leftEdges))

data RangeMetrics = RangeMetrics
  { rangeRowsMin :: Int
  , rangeRowsMax :: Int
  , rangeWindowsMin :: Integer
  , rangeWindowsMax :: Integer
  }

rangeMetrics :: [RangeWorkItem] -> RangeMetrics
rangeMetrics [] =
  RangeMetrics
    { rangeRowsMin = 0
    , rangeRowsMax = 0
    , rangeWindowsMin = 0
    , rangeWindowsMax = 0
    }
rangeMetrics items =
  let rowCounts = map (basisRowCount . rangeActualBasis) items
      windowCounts = map (basisWindowCount . rangeActualBasis) items
  in RangeMetrics
       { rangeRowsMin = minimum rowCounts
       , rangeRowsMax = maximum rowCounts
       , rangeWindowsMin = minimum windowCounts
       , rangeWindowsMax = maximum windowCounts
       }

writeMetrics :: Maybe FilePath -> CheckMetrics -> IO ()
writeMetrics Nothing _ = pure ()
writeMetrics (Just path) metrics =
  writeFile path $
    unlines
      [ "threads=" ++ show (metricThreads metrics)
      , "block_windows=" ++ show (metricBlockWindows metrics)
      , "actual_rows=" ++ show (metricActualRows metrics)
      , "actual_windows=" ++ show (metricActualWindows metrics)
      , "actual_blocks=" ++ show (metricActualBlocks metrics)
      , "range_count=" ++ show (metricRangeCount metrics)
      , "range_rows_min=" ++ show (metricRangeRowsMin metrics)
      , "range_rows_max=" ++ show (metricRangeRowsMax metrics)
      , "range_windows_min=" ++ show (metricRangeWindowsMin metrics)
      , "range_windows_max=" ++ show (metricRangeWindowsMax metrics)
      , "failed_range_index=" ++ maybe "none" show (metricFailedRangeIndex metrics)
      , "expected_rows=" ++ show (metricExpectedRows metrics)
      , "expected_windows=" ++ show (metricExpectedWindows metrics)
      , "expected_blocks=" ++ show (metricExpectedBlocks metrics)
      , "phase_csv_read_s=" ++ formatSeconds (metricPhaseCsvReadSeconds metrics)
      , "phase_csv_parse_s=" ++ formatSeconds (metricPhaseCsvParseSeconds metrics)
      , "phase_cbor_decode_s=" ++ formatSeconds (metricPhaseCborDecodeSeconds metrics)
      , "phase_witness_decode_s=" ++ formatSeconds (metricPhaseWitnessDecodeSeconds metrics)
      , "phase_metadata_validate_s=" ++ formatSeconds (metricPhaseMetadataValidateSeconds metrics)
      , "phase_build_dbf_s=" ++ formatSeconds (metricPhaseBuildDbfSeconds metrics)
      , "phase_resolve_threads_s=" ++ formatSeconds (metricPhaseResolveThreadsSeconds metrics)
      , "phase_actual_basis_count_s=" ++ formatSeconds (metricPhaseActualBasisCountSeconds metrics)
      , "phase_expected_basis_generate_s=" ++ formatSeconds (metricPhaseExpectedBasisGenerateSeconds metrics)
      , "phase_range_plan_s=" ++ formatSeconds (metricPhaseRangePlanSeconds metrics)
      , "phase_range_cover_s=" ++ formatSeconds (metricPhaseRangeCoverSeconds metrics)
      , "phase_range_equality_s=" ++ formatSeconds (metricPhaseRangeEqualitySeconds metrics)
      , "phase_range_ndbf_s=" ++ formatSeconds (metricPhaseRangeNdbfSeconds metrics)
      , "phase_actual_split_s=" ++ formatSeconds (metricPhaseActualSplitSeconds metrics)
      , "phase_expected_split_s=" ++ formatSeconds (metricPhaseExpectedSplitSeconds metrics)
      , "phase_structural_s=" ++ formatSeconds (metricPhaseStructuralSeconds metrics)
      , "phase_workers_s=" ++ formatSeconds (metricPhaseWorkersSeconds metrics)
      , "phase_check_total_s=" ++ formatSeconds (metricPhaseCheckTotalSeconds metrics)
      , "result=" ++ if metricResult metrics then "accept" else "reject"
      ]

formatSeconds :: Double -> String
formatSeconds =
  printf "%.6f"

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
