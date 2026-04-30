module CborWitness
  ( Term (..)
  , readCborTermFile
  , writeCborTermFile
  , mapTerm
  , lookupKey
  , replaceKey
  , expectMap
  , expectList
  , expectText
  , expectBool
  , expectInteger
  , expectOptionalInteger
  , objectTerm
  , textTerm
  , integerTerm
  )
where

import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Term (Term (..), decodeTerm, encodeTerm)
import Codec.CBOR.Write (toLazyByteString)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LazyText

readCborTermFile :: FilePath -> IO (Either String Term)
readCborTermFile path = do
  bytes <- LBS.readFile path
  pure $
    case deserialiseFromBytes decodeTerm bytes of
      Left err -> Left (show err)
      Right (remaining, term)
        | LBS.null remaining -> Right term
        | otherwise -> Left "trailing bytes after CBOR term"

writeCborTermFile :: FilePath -> Term -> IO ()
writeCborTermFile path =
  LBS.writeFile path . toLazyByteString . encodeTerm

mapTerm :: [(String, Term)] -> Term
mapTerm = TMap . map (\(key, value) -> (textTerm key, value))

objectTerm :: [(String, Term)] -> Term
objectTerm = mapTerm

textTerm :: String -> Term
textTerm = TString . Text.pack

integerTerm :: Integer -> Term
integerTerm n
  | n >= fromIntegral (minBound :: Int) && n <= fromIntegral (maxBound :: Int) =
      TInt (fromInteger n)
  | otherwise = TInteger n

expectMap :: String -> Term -> Either String [(Term, Term)]
expectMap _ (TMap fields) = Right fields
expectMap _ (TMapI fields) = Right fields
expectMap label term = Left (label ++ " must be a CBOR map, got " ++ show term)

expectList :: String -> Term -> Either String [Term]
expectList _ (TList xs) = Right xs
expectList _ (TListI xs) = Right xs
expectList label term = Left (label ++ " must be a CBOR list, got " ++ show term)

expectText :: String -> Term -> Either String String
expectText _ (TString text) = Right (Text.unpack text)
expectText _ (TStringI text) = Right (LazyText.unpack text)
expectText label term = Left (label ++ " must be a CBOR text string, got " ++ show term)

expectBool :: String -> Term -> Either String Bool
expectBool _ (TBool value) = Right value
expectBool label term = Left (label ++ " must be a CBOR bool, got " ++ show term)

expectInteger :: String -> Term -> Either String Integer
expectInteger _ (TInt n) = Right (fromIntegral n)
expectInteger _ (TInteger n) = Right n
expectInteger label term = Left (label ++ " must be a CBOR integer, got " ++ show term)

expectOptionalInteger :: String -> Term -> Either String (Maybe Integer)
expectOptionalInteger _ TNull = Right Nothing
expectOptionalInteger label term = Just <$> expectInteger label term

lookupKey :: String -> String -> [(Term, Term)] -> Either String Term
lookupKey label key fields =
  case lookup (textTerm key) fields of
    Just value -> Right value
    Nothing -> Left (label ++ " missing key " ++ show key)

replaceKey :: String -> Term -> Term -> Either String Term
replaceKey key replacement term = do
  fields <- expectMap "replace target" term
  pure (TMap (go fields))
  where
    encodedKey = textTerm key
    go [] = [(encodedKey, replacement)]
    go ((fieldKey, value) : rest)
      | fieldKey == encodedKey = (fieldKey, replacement) : rest
      | otherwise = (fieldKey, value) : go rest
