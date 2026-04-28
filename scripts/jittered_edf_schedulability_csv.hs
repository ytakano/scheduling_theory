module Main where

import qualified JitteredPeriodicEDFSchedulability as EDF

import Control.Monad (forM)
import Data.Char (isSpace, toLower)
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

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> runCutoff path
    ["--check-offset-window-dbf-cutoff", path] -> runCutoff path
    _ -> do
      printUsage
      exitFailure

printUsage :: IO ()
printUsage = do
  putStrLn "usage: scripts/jittered_edf_schedulability_csv TASKS.csv"
  putStrLn "       scripts/jittered_edf_schedulability_csv --check-offset-window-dbf-cutoff TASKS.csv"
  putStrLn "CSV columns: cost,period,deadline[,offset[,jitter]]"

runCutoff :: FilePath -> IO ()
runCutoff path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          accepted = EDF.jittered_periodic_offset_window_schedulability_decide input
      case accepted of
        EDF.True -> do
          putStrLn "jittered offset-window schedulable"
          exitSuccess
        EDF.False -> do
          putStrLn "not jittered offset-window schedulable or invalid input"
          printWindowWitness
            (EDF.jittered_periodic_offset_window_schedulability_counterexample input)
          exitFailure

printWindowWitness :: EDF.Option (EDF.Prod EDF.Time EDF.Time) -> IO ()
printWindowWitness EDF.None = pure ()
printWindowWitness (EDF.Some (EDF.Pair t1 t2)) =
  putStrLn $
    "window DBF overload witness t1=" ++ show (fromNat t1)
      ++ " t2=" ++ show (fromNat t2)

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
       || cells == ["cost", "period", "deadline", "offset", "jitter"]
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
    [costText, periodText, deadlineText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      pure (ParsedTask cost period deadline 0 0)
    [costText, periodText, deadlineText, offsetText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      offset <- parseNonnegative lineNo "offset" offsetText
      pure (ParsedTask cost period deadline offset 0)
    [costText, periodText, deadlineText, offsetText, jitterText] -> do
      cost <- parsePositive lineNo "cost" costText
      period <- parsePositive lineNo "period" periodText
      deadline <- parsePositive lineNo "deadline" deadlineText
      offset <- parseNonnegative lineNo "offset" offsetText
      jitter <- parseNonnegative lineNo "jitter" jitterText
      pure (ParsedTask cost period deadline offset jitter)
    cols ->
      Left $
        "line " ++ show lineNo ++ ": expected 3, 4, or 5 columns, got "
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

toEDFTask :: ParsedTask -> EDF.ExtractedJitteredPeriodicTask
toEDFTask task =
  EDF.MkExtractedJitteredPeriodicTask
    (toNat (parsedCost task))
    (toNat (parsedPeriod task))
    (toNat (parsedDeadline task))
    (toNat (parsedOffset task))
    (toNat (parsedJitter task))

toEDFList :: [a] -> EDF.List a
toEDFList =
  foldr EDF.Cons EDF.Nil

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
