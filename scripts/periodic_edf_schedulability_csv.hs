module Main where

import qualified PeriodicEDFSchedulability as EDF

import Control.Monad (forM)
import Data.Char (isSpace, toLower)
import Data.List (foldl')
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Read (readMaybe)

data ParsedTask = ParsedTask
  { parsedCost :: Int
  , parsedPeriod :: Int
  , parsedDeadline :: Int
  , parsedOffset :: Int
  }

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> run path
    ["--check-prefix-cert", path] -> runPrefixCertCheck path
    ["--check-offset-window-dbf", horizonText, path] ->
      case parseHorizon horizonText of
        Left err -> putStrLn err >> printUsage >> exitFailure
        Right horizon -> runOffsetWindowFinite horizon path
    ["--check-offset-window-dbf-cutoff", path] -> runOffsetWindowCutoff path
    _ -> do
      printUsage
      exitFailure

printUsage :: IO ()
printUsage = do
  putStrLn "usage: scripts/periodic_edf_schedulability_csv TASKS.csv"
  putStrLn "       scripts/periodic_edf_schedulability_csv --check-prefix-cert TASKS.csv"
  putStrLn "       scripts/periodic_edf_schedulability_csv --check-offset-window-dbf H TASKS.csv"
  putStrLn "       scripts/periodic_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS.csv"
  putStrLn "CSV columns: cost,period,deadline[,offset]"

run :: FilePath -> IO ()
run path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          accepted = EDF.periodic_conservative_schedulability_decide input
      case accepted of
        EDF.True -> do
          putStrLn "schedulable"
          exitSuccess
        EDF.False -> do
          putStrLn "not schedulable or invalid input"
          case EDF.periodic_conservative_schedulability_counterexample input of
            EDF.None -> pure ()
            EDF.Some t ->
              putStrLn ("DBF overload witness t=" ++ show (fromNat t))
          exitFailure

runPrefixCertCheck :: FilePath -> IO ()
runPrefixCertCheck path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          cert = generatePrefixCert tasks
          semanticOk =
            EDF.check_prefix_cert_semantic
              (EDF.extracted_offset_periodic_jobs input)
              cert
          generatedOk =
            EDF.check_prefix_slots_match_generated_edf_fast
              (EDF.extracted_periodic_tasks input)
              (EDF.extracted_periodic_offsets input)
              (EDF.extracted_offset_periodic_jobs input)
              (EDF.enumT_of_extracted_list input)
              (EDF.extracted_offset_periodic_codec input)
              cert
      case (semanticOk, generatedOk) of
        (EDF.True, EDF.True) -> do
          putStrLn "prefix certificate ok"
          exitSuccess
        _ -> do
          putStrLn "prefix certificate check failed"
          exitFailure

runOffsetWindowFinite :: Int -> FilePath -> IO ()
runOffsetWindowFinite horizon path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          h = toNat horizon
          accepted = EDF.extracted_offset_window_dbf_decide input h
      case accepted of
        EDF.True -> do
          putStrLn "offset-window schedulable"
          exitSuccess
        EDF.False -> do
          putStrLn "not offset-window schedulable or invalid input"
          printWindowWitness (EDF.extracted_offset_window_dbf_counterexample input h)
          exitFailure

runOffsetWindowCutoff :: FilePath -> IO ()
runOffsetWindowCutoff path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          accepted = EDF.periodic_offset_window_schedulability_decide input
      case accepted of
        EDF.True -> do
          putStrLn "offset-window schedulable"
          exitSuccess
        EDF.False -> do
          putStrLn "not offset-window schedulable or invalid input"
          printWindowWitness (EDF.periodic_offset_window_schedulability_counterexample input)
          exitFailure

printWindowWitness :: EDF.Option (EDF.Prod EDF.Time EDF.Time) -> IO ()
printWindowWitness EDF.None = pure ()
printWindowWitness (EDF.Some (EDF.Pair t1 t2)) =
  putStrLn $
    "window DBF overload witness t1=" ++ show (fromNat t1)
      ++ " t2=" ++ show (fromNat t2)

parseHorizon :: String -> Either String Int
parseHorizon text =
  case readMaybe text of
    Just n | n >= 0 -> Right n
    Just _ -> Left "horizon H must be nonnegative"
    Nothing -> Left ("invalid horizon H: " ++ text)

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

data PrefixJob = PrefixJob
  { prefixJobId :: Int
  , prefixJobTask :: Int
  , prefixJobIndex :: Int
  , prefixJobRelease :: Int
  , prefixJobCost :: Int
  , prefixJobDeadline :: Int
  }

generatePrefixCert :: [ParsedTask] -> EDF.EDFPrefixCert EDF.JobId
generatePrefixCert tasks =
  let horizon = prefixHorizon tasks
      jobs = prefixBasisJobs tasks horizon
      slots = simulateEDFPrefix jobs horizon
      completedBy = map (completionTime slots) jobs
      backlog = [[completionTime slots earlier <= prefixJobRelease target | earlier <- jobs] | target <- jobs]
  in EDF.Build_EDFPrefixCert
       (toNat horizon)
       (toEDFList (map (toNat . prefixJobId) jobs))
       (toEDFList (map toEDFSlot slots))
       (toEDFList (map toNat completedBy))
       (toEDFList (map (toEDFList . map toEDFBool) backlog))

checkGeneratedPrefixNative :: [ParsedTask] -> EDF.EDFPrefixCert EDF.JobId -> Bool
checkGeneratedPrefixNative tasks cert =
  let horizon = prefixHorizon tasks
      jobs = prefixBasisJobs tasks horizon
      slots = simulateEDFPrefix jobs horizon
  in fromNat (EDF.prefix_horizon cert) == horizon
       && map fromEDFSlot (fromEDFList (EDF.prefix_slots cert)) == slots
       && length slots == horizon

prefixHorizon :: [ParsedTask] -> Int
prefixHorizon [] = 0
prefixHorizon tasks =
  maximum (map parsedOffset tasks) + 2 * hyperperiod tasks + maximum (map parsedDeadline tasks)

hyperperiod :: [ParsedTask] -> Int
hyperperiod =
  foldl' lcm 1 . map parsedPeriod

prefixBasisJobs :: [ParsedTask] -> Int -> [PrefixJob]
prefixBasisJobs tasks horizon =
  concat
    [ jobsForTask taskIndex task
    | (taskIndex, task) <- zip [0 ..] tasks
    ]
  where
    taskCount = length tasks
    jobsForTask taskIndex task =
      [ PrefixJob
          { prefixJobId = taskIndex + taskCount * jobIndex
          , prefixJobTask = taskIndex
          , prefixJobIndex = jobIndex
          , prefixJobRelease = release
          , prefixJobCost = parsedCost task
          , prefixJobDeadline = release + parsedDeadline task
          }
      | jobIndex <- takeWhile (\k -> parsedOffset task + k * parsedPeriod task < horizon) [0 ..]
      , let release = parsedOffset task + jobIndex * parsedPeriod task
      ]

simulateEDFPrefix :: [PrefixJob] -> Int -> [Maybe Int]
simulateEDFPrefix jobs horizon =
  go 0 initialRemaining []
  where
    initialRemaining = [(prefixJobId job, prefixJobCost job) | job <- jobs]

    go t remaining acc
      | t >= horizon = reverse acc
      | otherwise =
          case chooseJob t remaining of
            Nothing -> go (t + 1) remaining (Nothing : acc)
            Just job ->
              let remaining' = decrementRemaining (prefixJobId job) remaining
              in go (t + 1) remaining' (Just (prefixJobId job) : acc)

    chooseJob t remaining =
      chooseByDeadline
        [ job
        | job <- jobs
        , prefixJobRelease job <= t
        , remainingOf (prefixJobId job) remaining > 0
        ]

    chooseByDeadline [] = Nothing
    chooseByDeadline (job : rest) =
      Just (foldl' earlierDeadline job rest)

    earlierDeadline best job
      | prefixJobDeadline job < prefixJobDeadline best = job
      | otherwise = best

remainingOf :: Int -> [(Int, Int)] -> Int
remainingOf _ [] = 0
remainingOf jobId ((jobId', remaining) : rest)
  | jobId == jobId' = remaining
  | otherwise = remainingOf jobId rest

decrementRemaining :: Int -> [(Int, Int)] -> [(Int, Int)]
decrementRemaining _ [] = []
decrementRemaining jobId ((jobId', remaining) : rest)
  | jobId == jobId' = (jobId', max 0 (remaining - 1)) : rest
  | otherwise = (jobId', remaining) : decrementRemaining jobId rest

completionTime :: [Maybe Int] -> PrefixJob -> Int
completionTime slots job =
  go 0 0 slots
  where
    go t service remainingSlots
      | service >= prefixJobCost job = t
      | otherwise =
          case remainingSlots of
            [] -> length slots
            slot : rest ->
              let service' =
                    case slot of
                      Just jobId | jobId == prefixJobId job -> service + 1
                      _ -> service
              in go (t + 1) service' rest

toEDFSlot :: Maybe Int -> EDF.Option EDF.JobId
toEDFSlot Nothing = EDF.None
toEDFSlot (Just jobId) = EDF.Some (toNat jobId)

toEDFBool :: Bool -> EDF.Bool
toEDFBool True = EDF.True
toEDFBool False = EDF.False

toEDFTask :: ParsedTask -> EDF.ExtractedPeriodicTask
toEDFTask task =
  EDF.MkExtractedPeriodicTask
    (toNat (parsedCost task))
    (toNat (parsedPeriod task))
    (toNat (parsedDeadline task))
    (toNat (parsedOffset task))

toEDFList :: [a] -> EDF.List a
toEDFList =
  foldr EDF.Cons EDF.Nil

fromEDFList :: EDF.List a -> [a]
fromEDFList EDF.Nil = []
fromEDFList (EDF.Cons x xs) = x : fromEDFList xs

fromEDFSlot :: EDF.Option EDF.JobId -> Maybe Int
fromEDFSlot EDF.None = Nothing
fromEDFSlot (EDF.Some jobId) = Just (fromNat jobId)

toNat :: Int -> EDF.Nat
toNat n
  | n <= 0 = EDF.O
  | otherwise = EDF.S (toNat (n - 1))

fromNat :: EDF.Nat -> Int
fromNat EDF.O = 0
fromNat (EDF.S n) = 1 + fromNat n

splitComma :: String -> [String]
splitComma s =
  case break (== ',') s of
    (cell, []) -> [cell]
    (cell, _ : rest) -> cell : splitComma rest

trim :: String -> String
trim =
  dropWhileEnd isSpace . dropWhile isSpace

dropWhileEnd :: (a -> Bool) -> [a] -> [a]
dropWhileEnd p =
  reverse . dropWhile p . reverse

isPrefixOf :: Eq a => [a] -> [a] -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (x : xs) (y : ys) = x == y && isPrefixOf xs ys
