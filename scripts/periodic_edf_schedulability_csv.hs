module Main where

import qualified PeriodicEDFSchedulability as EDF

import Control.Monad (forM)
import Data.Char (isSpace, toLower)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import Text.Read (readMaybe)

data ParsedTask = ParsedTask
  { parsedCost :: Int
  , parsedPeriod :: Int
  , parsedDeadline :: Int
  }

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> run path
    _ -> do
      putStrLn "usage: scripts/run_periodic_edf_schedulability TASKS.csv"
      putStrLn "CSV columns: cost,period,deadline"
      exitFailure

run :: FilePath -> IO ()
run path = do
  content <- readFile path
  case parseCsv content of
    Left err -> putStrLn err >> exitFailure
    Right tasks -> do
      let input = toEDFList (map toEDFTask tasks)
          accepted = EDF.edf_schedulability_decide input
      case accepted of
        EDF.True -> do
          putStrLn "schedulable"
          exitSuccess
        EDF.False -> do
          putStrLn "not schedulable or invalid input"
          case EDF.edf_schedulability_counterexample input of
            EDF.None -> pure ()
            EDF.Some t ->
              putStrLn ("DBF overload witness t=" ++ show (fromNat t))
          exitFailure

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
  map normalizeHeaderCell (splitComma line) == ["cost", "period", "deadline"]

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
      pure (ParsedTask cost period deadline)
    cols ->
      Left $
        "line " ++ show lineNo ++ ": expected 3 columns, got "
          ++ show (length cols)

parsePositive :: Int -> String -> String -> Either String Int
parsePositive lineNo name text =
  case readMaybe text of
    Just n | n > 0 -> Right n
    Just _ -> Left ("line " ++ show lineNo ++ ": " ++ name ++ " must be positive")
    Nothing -> Left ("line " ++ show lineNo ++ ": invalid " ++ name ++ ": " ++ text)

toEDFTask :: ParsedTask -> EDF.ExtractedPeriodicTask
toEDFTask task =
  EDF.MkExtractedPeriodicTask
    (toNat (parsedCost task))
    (toNat (parsedPeriod task))
    (toNat (parsedDeadline task))

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
