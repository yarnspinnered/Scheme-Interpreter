module LispParsing (parseExpr) where
import Data.Array
import Control.Monad
import Numeric (readFloat)
import Text.ParserCombinators.Parsec hiding (spaces)

-- my stuff
import LispTypes

parseExpr :: Parser LispVal
parseExpr = try parseChar
         <|> try parseString
         <|> try parseFloat
         <|> try parseNumber
         <|> try parseQuoted
         <|> try parseUnquoted
         <|> try parseQuasiquoted
         <|> try parseVector
         <|> do char '('
                x <- try parseList <|> parseDottedList
                char ')'
                return x
         <|> try parseAtom

parseQuoted :: Parser LispVal
parseQuoted = do
    char '\''
    x <- parseExpr
    return $ List [Atom "quote", x]

parseUnquoted :: Parser LispVal
parseUnquoted = do
    char ','
    x <- parseExpr
    return $ List [Atom "unquoted", x]

parseQuasiquoted :: Parser LispVal
parseQuasiquoted = do
    char '`'
    x <- parseExpr
    return $ List [Atom "quasiquoted", x]

parseList :: Parser LispVal
parseList = liftM List $ sepBy parseExpr spaces

parseDottedList :: Parser LispVal
parseDottedList = do
    head <- endBy parseExpr spaces
    tail <- char '.' >> spaces >> parseExpr
    return $ DottedList head tail

parseVector :: Parser LispVal
parseVector = do
    string "#("
    x <- sepBy parseExpr spaces
    return $ Vector $ array (0, length x - 1) (zip [0.. (length x - 1)] x)

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

parseString :: Parser LispVal
parseString = do
                char '"'
                x <- many $ escapedChar <|> (noneOf "\"\\") 
                char '"'
                return $ String x

parseChar :: Parser LispVal
parseChar = do
    string "#\\"
    x <- (string "space" <|> string "newline")  
        <|> do 
            y <- letter <|> oneOf "( ";
            return [y]
    return $ Character $ case x of
        "space" -> ' '
        "newline" -> 'n'
        otherwise -> (x !! 0)

parseNumber :: Parser LispVal
parseNumber = liftM (Number . read) $ many1 digit

parseNumberDo :: Parser LispVal
parseNumberDo = do 
    x <- many1 digit
    return  $ (Number . read) x

parseNumberUnsugared :: Parser LispVal
parseNumberUnsugared = many1 digit >>= (\ x -> return $ (Number . read) x)

parseFloat :: Parser LispVal
parseFloat = do
    x <- many digit
    char '.'
    y <- many digit
    return $ Float $ (fst . head . readFloat) $ x ++ "." ++ y

parseAtom :: Parser LispVal
parseAtom = do 
              first <- letter <|> symbol
              rest <- many (letter <|> digit <|> symbol)
              let atom = first:rest
              return $ case atom of 
                         "#t" -> Bool True
                         "#f" -> Bool False
                         _    -> Atom atom

spaces :: Parser ()
spaces = skipMany1 space

escapedChar :: Parser Char
escapedChar = do
    char '\\'
    y <- oneOf "\\\"nrt"
    return $ case y of
        '\\' -> '\\' 
        '\"' -> '\"'
        'n' -> '\n'
        'r' -> '\r'
        't' -> '\t'