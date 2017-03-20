{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.PPL.MIP.TH
  (
    linexp,
    affexp
  )
where

import           Control.Applicative
import           Control.Arrow
import           Control.Lens
import           Data.Attoparsec.Text
import qualified Data.Foldable as F
import           Data.PPL.MIP
import           Data.Ratio
import qualified Data.Text as T
import           Language.Haskell.TH.Quote
import           Language.Haskell.TH.Syntax

parseVar :: Parser Var
parseVar = var <$> ((:) <$> letter <*> many' (letter <|> digit)) <* skipSpace

parseScalar :: Parser Rational
parseScalar = let p = (rational <|>
                      (do num <- decimal <* skipSpace
                          _ <- string "/" <* skipSpace
                          denum <- decimal <* skipSpace
                          return $! (num % denum)))
              in p <|> (string "(" *> skipSpace *> parseScalar <* string ")" <* skipSpace)

parseScalarPrefix :: Parser Rational
parseScalarPrefix = (string "-" *> skipSpace *> (negate <$> parseScalarPrefix)) <|>
                    (string "+" *> skipSpace *> parseScalarPrefix) <|>
                    (maybe 1 id <$> optional (parseScalar <* optional (string "*" <* skipSpace)))

parseScalarSuffix :: Parser Rational
parseScalarSuffix = maybe 1 id <$> optional (optional (string "*" <* skipSpace) *> parseScalar)

parseLinearExpr :: Parser (LinearExpression Rational)
parseLinearExpr = do
  p <- parseScalarPrefix
  l <- ((1 %*) <$> parseVar) <|> (string "(" *> skipSpace *> parseLinear <* string ")" <* skipSpace)
  s <- parseScalarSuffix
  return $! sc (p * s) %* l

parseLinearTail :: Parser (LinearExpression Rational)
parseLinearTail = (%*) <$> (((sc 1 <$ string "+") <|> (sc (-1) <$ string "-")) <* skipSpace) <*> parseLinearExpr

parseLinear :: Parser (LinearExpression Rational)
parseLinear = do
   l <- parseLinearExpr
   r <- many parseLinearTail
   return $! F.fold (l:r)

mulBy :: Rational -> Either (AffineExpression Rational) (LinearExpression Rational) -> Either (AffineExpression Rational) (LinearExpression Rational)
mulBy r = (sc r %*) +++ (sc r %*)

parseExpr :: Parser (Either (AffineExpression Rational) (LinearExpression Rational))
parseExpr = (do
  p <- parseScalarPrefix
  l <- (Right . (1 %*) <$> parseVar) <|>
       (string "(" *> skipSpace *> parseAff <* string ")" <* skipSpace)
  s <- parseScalarSuffix
  return . mulBy (p * s) $ l) <|>
  (Left . ((mempty ::AffineExpression Rational) %+) . sc <$> parseScalar)

parseTail :: Parser (Either (AffineExpression Rational) (LinearExpression Rational))
parseTail = mulBy <$> (((1 <$ string "+") <|> (-1 <$ string "-")) <* skipSpace) <*> parseExpr

parseAff :: Parser (Either (AffineExpression Rational) (LinearExpression Rational))
parseAff = do
  l <- parseExpr
  r <- many parseTail
  return $! F.foldr f (Right mempty) (l:r)
  where f (Left l) r = Left $! either (l %+) (l %+) r
        f (Right l) (Left r) = Left $! l %+ r
        f (Right l) (Right r) = Right $! l %+ r

linexp :: QuasiQuoter
linexp = QuasiQuoter {quoteExp = linexpQuoteExpr, quotePat = undefined, quoteType = undefined, quoteDec = undefined}
         where linexpQuoteExpr str =
                 let le = either error id . parseOnly (skipSpace *> parseLinear <* endOfInput) $ T.pack str
                     cf = le ^.. coeff . withIndex . iso (first (^. name)) (first var) . to vExpr
                     vExpr (x, a) = let x' = return . LitE . StringL $ x
                                        a' = return . LitE . RationalL $ a
                                    in [| ($a' %* var $x') :: LinearExpression Rational |]
                 in if null cf
                      then [|mempty :: LinearExpression Rational|]
                      else F.foldr1 (\e ac -> [| $e %+ $ac |]) cf

affexp :: QuasiQuoter
affexp = QuasiQuoter {quoteExp = affexpQuoteExpr, quotePat = undefined, quoteType = undefined, quoteDec = undefined}
         where affexpQuoteExpr str = do
                 let le = either id (%+ sc 0) . either error id . parseOnly (skipSpace *> parseAff <* endOfInput) $ T.pack str
                     procElem :: (String, Rational) -> Maybe (Q Exp) -> Q (Maybe (Q Exp))
                     procElem (x, a) Nothing  = return . Just $! [|$(lift a) %* var $(lift x)|]
                     procElem (x, a) (Just t) = return . Just $! [|$(lift a) %* var $(lift x) %+ $t|]
                     ce = lift $! le ^. constant
                 cf <- foldrMOf (coeff . withIndex . iso (first (^. name)) (first var)) procElem Nothing le
                 case cf of
                   Just e -> [|(($e :: LinearExpression Rational) %+ sc $ce) :: AffineExpression Rational|]
                   Nothing -> [|(mempty :: AffineExpression Rational) %+ sc $ce|]

