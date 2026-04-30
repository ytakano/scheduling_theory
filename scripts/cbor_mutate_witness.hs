module Main where

import CborWitness

import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [mutation, inputPath, outputPath] -> do
      decoded <- readCborTermFile inputPath
      case decoded of
        Left err -> die ("failed to decode CBOR: " ++ err)
        Right term ->
          case mutate mutation term of
            Left err -> die err
            Right mutated -> writeCborTermFile outputPath mutated
    _ -> die "usage: cbor_mutate_witness MUTATION INPUT.cbor OUTPUT.cbor"

die :: String -> IO a
die msg = putStrLn msg >> exitFailure

mutate :: String -> Term -> Either String Term
mutate "task-hash-zero" =
  replaceKey "task_hash" (textTerm "sha256:0")
mutate "schema-version-one" =
  replaceKey "schema_version" (integerTerm 1)
mutate "policy-periodic" =
  replaceKey "policy" (textTerm "periodic-edf")
mutate "domain-multiprocessor" =
  replaceKey "domain" (textTerm "multiprocessor")
mutate "all-basis-unchecked" =
  updateDbf (replaceKey "all_basis_checked" (TBool False))
mutate "jittered-cutoff-zero" =
  updateDbf (replaceKey "cutoff" (integerTerm 0))
mutate "jittered-cutoff-negative" =
  updateDbf (replaceKey "cutoff" (integerTerm (-1)))
mutate "jittered-prepend-basis-extra" =
  updateDbf prependBasis
mutate "jittered-first-left-edge-999" =
  updateDbf mutateFirstLeftEdge
mutate "periodic-first-slot-null" =
  updatePrefix (mutateFirstInList "slots" TNull)
mutate "periodic-first-completed-zero" =
  updatePrefix (mutateFirstInList "completed_by" (integerTerm 0))
mutate "periodic-first-job-class-one" =
  updateTransport (mutateFirstInList "job_class" (integerTerm 1))
mutate "all-bools-false" =
  pure . mapBoolsFalse
mutate name =
  const (Left ("unknown mutation: " ++ name))

updateCert :: (Term -> Either String Term) -> Term -> Either String Term
updateCert f term = do
  fields <- expectMap "witness" term
  cert <- lookupKey "witness" "cert" fields
  cert' <- f cert
  replaceKey "cert" cert' term

updateDbf :: (Term -> Either String Term) -> Term -> Either String Term
updateDbf f =
  updateCert $ \cert -> do
    fields <- expectMap "cert" cert
    dbf <- lookupKey "cert" "dbf" fields
    dbf' <- f dbf
    replaceKey "dbf" dbf' cert

updatePrefix :: (Term -> Either String Term) -> Term -> Either String Term
updatePrefix f =
  updateCert $ \cert -> do
    fields <- expectMap "cert" cert
    prefix <- lookupKey "cert" "prefix" fields
    prefix' <- f prefix
    replaceKey "prefix" prefix' cert

updateTransport :: (Term -> Either String Term) -> Term -> Either String Term
updateTransport f =
  updateCert $ \cert -> do
    fields <- expectMap "cert" cert
    transport <- lookupKey "cert" "transport" fields
    transport' <- f transport
    replaceKey "transport" transport' cert

prependBasis :: Term -> Either String Term
prependBasis dbf = do
  fields <- expectMap "dbf" dbf
  basis <- lookupKey "dbf" "basis" fields
  rows <- expectList "dbf.basis" basis
  let extra =
        objectTerm
          [ ("t2", integerTerm 999)
          , ("left_edges", TList [integerTerm 999])
          ]
  replaceKey "basis" (TList (extra : rows)) dbf

mutateFirstLeftEdge :: Term -> Either String Term
mutateFirstLeftEdge dbf = do
  fields <- expectMap "dbf" dbf
  basis <- lookupKey "dbf" "basis" fields
  rows <- expectList "dbf.basis" basis
  case rows of
    [] -> Left "dbf.basis is empty"
    row : rest -> do
      rowFields <- expectMap "dbf.basis[]" row
      leftEdges <- lookupKey "dbf.basis[]" "left_edges" rowFields
      edges <- expectList "dbf.basis[].left_edges" leftEdges
      case edges of
        [] -> Left "dbf.basis[].left_edges is empty"
        _ : edgeRest -> do
          row' <- replaceKey "left_edges" (TList (integerTerm 999 : edgeRest)) row
          replaceKey "basis" (TList (row' : rest)) dbf

mutateFirstInList :: String -> Term -> Term -> Either String Term
mutateFirstInList key replacement term = do
  fields <- expectMap key term
  listTerm <- lookupKey key key fields
  values <- expectList key listTerm
  case values of
    [] -> Left (key ++ " is empty")
    _ : rest -> replaceKey key (TList (replacement : rest)) term

mapBoolsFalse :: Term -> Term
mapBoolsFalse (TBool _) = TBool False
mapBoolsFalse (TList xs) = TList (map mapBoolsFalse xs)
mapBoolsFalse (TListI xs) = TListI (map mapBoolsFalse xs)
mapBoolsFalse (TMap fields) =
  TMap (map (\(key, value) -> (key, mapBoolsFalse value)) fields)
mapBoolsFalse (TMapI fields) =
  TMapI (map (\(key, value) -> (key, mapBoolsFalse value)) fields)
mapBoolsFalse (TTagged tag term) = TTagged tag (mapBoolsFalse term)
mapBoolsFalse term = term
