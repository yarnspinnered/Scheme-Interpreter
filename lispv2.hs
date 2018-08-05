import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment
import Control.Monad
import Numeric 
import Data.Array
import Data.Typeable
import Control.Monad.Except
import System.IO

-- Parser makers. OneOf/letter/digit/space
-- Parser combinators. skipMany1, <|>
-- return to lift a value into a monad
-- $ ensures stuff o nthe right happens first.
data LispVal = Atom String
             | List [LispVal]
             | DottedList [LispVal] LispVal
             | Number Integer
             | Float Float
             | String String
             | Character Char
             | Vector (Array Int LispVal)
             | Bool Bool
instance Show LispVal where show = showVal

showVal :: LispVal -> String
showVal (String contents) = "\"" ++ contents ++ "\""
showVal (Character char) = "#\\" ++ [char]
showVal (Atom name) = name
showVal (Number contents) = show contents
showVal (Float contents) = show contents
showVal (Vector contents) = show contents
showVal (Bool True) = "#t"
showVal (Bool False) = "#f"
showVal (List contents) = "(" ++ unwordsList contents ++ ")"
showVal (DottedList head tail) = "(" ++ unwordsList head ++ " . " ++ showVal tail ++ ")"

data LispError = NumArgs Integer [LispVal]
               | TypeMismatch String LispVal
               | Parser ParseError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String

showError :: LispError -> String
showError (UnboundVar message varname)  = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ show form
showError (NotFunction message func)    = message ++ ": " ++ show func
showError (NumArgs expected found)      = "Expected " ++ show expected 
                                       ++ " args; found values " ++ unwordsList found
showError (TypeMismatch expected found) = "Invalid type: expected " ++ expected
                                       ++ ", found " ++ show found
showError (Parser parseErr)             = "Parse error at " ++ show parseErr
showError (Default msg)                 = "Generic Error: " ++ show msg
instance Show LispError where show = showError

type ThrowsError = Either LispError

trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

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


symbol2string, string2symbol :: LispVal -> LispVal
symbol2string (Atom x) = String x
symbol2string _ = String ""
string2symbol (String x) = Atom x
string2symbol _ = Atom ""

data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = 
             do unpacked1 <- unpacker arg1
                unpacked2 <- unpacker arg2
                return $ unpacked1 == unpacked2
        `catchError` (const $ return False)

eqvList :: ([LispVal] -> ThrowsError LispVal) -> [LispVal] -> ThrowsError LispVal
eqvList eqvFunc [(List arg1), (List arg2)] =return $ Bool $ (length arg1 == length arg2) && 
    (all eqvPair $ zip arg1 arg2) where
        eqvPair (x, y) = case eqvFunc [x,y] of
            Left err -> False
            Right (Bool val) -> val

equal :: [LispVal] -> ThrowsError LispVal
equal [(List arg1), (List arg2)] = eqvList equal [(List arg1), (List arg2)]
equal [(DottedList xs x), (DottedList ys y)] = eqvList equal [(List $ xs ++ [x]), (List $ ys ++ [y])]
equal [arg1, arg2] = do
      primitiveEquals <- liftM or $ mapM (unpackEquals arg1 arg2) 
                         [AnyUnpacker unpackNum, AnyUnpacker unpackStr, AnyUnpacker unpackBool]
      eqvEquals <- eqv [arg1, arg2]
      return $ Bool $ (primitiveEquals || let (Bool x) = eqvEquals in x)
equal badArgList = throwError $ NumArgs 2 badArgList


unpackNum :: LispVal -> ThrowsError Integer
unpackNum (Number n) = return n
unpackNum (String n) = let parsed = reads n in 
                           if null parsed 
                             then throwError $ TypeMismatch "number" $ String n
                             else return $ fst $ parsed !! 0
unpackNum (List [n]) = unpackNum n
unpackNum notNum     = throwError $ TypeMismatch "number" notNum

unpackStr :: LispVal -> ThrowsError String
unpackStr (String s) = return s
unpackStr (Number s) = return $ show s
unpackStr (Bool s)   = return $ show s
unpackStr notString  = throwError $ TypeMismatch "string" notString

unpackBool :: LispVal -> ThrowsError Bool
unpackBool (Bool b) = return b
unpackBool notBool  = throwError $ TypeMismatch "boolean" notBool

boolBinop :: (LispVal -> ThrowsError a) -> (a -> a -> Bool) -> [LispVal] -> ThrowsError LispVal
boolBinop unpacker op args = if length args /= 2 
                             then throwError $ NumArgs 2 args
                             else do 
                                left <- unpacker $ args !! 0
                                right <- unpacker $ args !! 1
                                return $ Bool $ left `op` right

numBoolBinop  = boolBinop unpackNum
strBoolBinop  = boolBinop unpackStr
boolBoolBinop = boolBinop unpackBool


numericBinop :: (Integer -> Integer -> Integer) -> [LispVal] -> ThrowsError LispVal
numericBinop op           []  = throwError $ NumArgs 2 []
numericBinop op singleVal@[_] = throwError $ NumArgs 2 singleVal
numericBinop op params        = mapM unpackNum params >>= return . Number . foldl1 op

typeTest :: String -> [LispVal] -> ThrowsError LispVal
typeTest "Number" [Number _]  = return $ Bool True
typeTest "Number" _ =return $  Bool False
typeTest "String" [String _]  = return $ Bool True
typeTest "String" _ = return $ Bool False
typeTest "Symbol" [Atom _]  = return $ Bool True
typeTest "Symbol" _ = return $ Bool False
typeTest "Bool" [Bool _]  = return $ Bool True
typeTest "Bool" _ = return $ Bool False
typeTest "List" [List _]  = return $ Bool True
typeTest "List" _ = return $ Bool False

car :: [LispVal] -> ThrowsError LispVal
car [List (x:xs)] = return x
car [DottedList (x:xs) _ ] = return x
car [badArg] = throwError $ TypeMismatch "pair" badArg
car badArgList = throwError $ NumArgs 1 badArgList

cdr :: [LispVal] -> ThrowsError LispVal 
cdr [List (x:xs)] = return $ List xs
cdr [DottedList [_] x ] = return $ x
cdr [DottedList (_:xs) x] = return $ DottedList xs x
cdr [badArg] = throwError $ TypeMismatch "pair" badArg
cdr badArgList = throwError $ NumArgs 1 badArgList

cons :: [LispVal] -> ThrowsError LispVal
cons [x1, List []] = return $ List [x1]
cons [x, List xs] = return $ List $ x:xs
cons [x, DottedList xs xlast] =  return $ DottedList (x:xs) xlast
cons [x1, x2] = return $ DottedList [x1] x2
cons badArgList = throwError $ NumArgs 2 badArgList

eqv :: [LispVal] -> ThrowsError LispVal
eqv [(Bool arg1), (Bool arg2)]             = return $ Bool $ arg1 == arg2
eqv [(Number arg1), (Number arg2)]         = return $ Bool $ arg1 == arg2
eqv [(String arg1), (String arg2)]         = return $ Bool $ arg1 == arg2
eqv [(Atom arg1), (Atom arg2)]             = return $ Bool $ arg1 == arg2
eqv [(DottedList xs x), (DottedList ys y)] = eqv [List $ xs ++ [x], List $ ys ++ [y]]
eqv [(List arg1), (List arg2)]             = eqvList eqv [(List arg1), (List arg2)]
eqv [_, _]                                 = return $ Bool False
eqv badArgList                             = throwError $ NumArgs 2 badArgList

stringLength :: [LispVal] -> ThrowsError LispVal
stringLength [String str] = return $ Number $ toInteger $ length str
stringLength [arg] =  throwError $ TypeMismatch "Expecting a string" arg
stringLength badArgs = throwError $ NumArgs 1 badArgs

stringRef :: [LispVal] -> ThrowsError LispVal
stringRef [String str, Number num] = 
    if (num < (toInteger $ length str) && num >= 0 && (toInteger $ length str) > 0)
        then return $ Character $ str !! (fromInteger  num)
        else throwError $ Default "Index out of bounds"
stringRef lst@[x, y] =  throwError $ TypeMismatch "Expecting a string and index" $ List lst
stringRef badArgs = throwError $ NumArgs 2 badArgs

charsToString :: [LispVal] -> ThrowsError LispVal
charsToString lst@(x:xs) = helper lst
    where 
        helper [] = return $ String ""
        helper (Character x:xs) = case (helper xs) of
                Right (String str) -> return $ String $ x:str
                Left err -> case err of
                    TypeMismatch errMsg found -> throwError $ TypeMismatch errMsg (found)
        helper x = throwError $ TypeMismatch "Non-char inside" $ x!!0

primitives :: [(String, [LispVal] -> ThrowsError LispVal)]
primitives = [
            ("+", numericBinop (+)),
            ("-", numericBinop (-)),
            ("*", numericBinop (*)),
            ("/", numericBinop div),
            ("mod", numericBinop mod),
            ("quotient", numericBinop quot),
            ("remainder", numericBinop rem),
            ("number?", typeTest "Number"),
            ("string?", typeTest "String"),
            ("symbol?", typeTest "Symbol"),
            ("bool?", typeTest "Bool"),
            ("list?", typeTest "List"),
            ("=", numBoolBinop (==)),
            ("<", numBoolBinop (<)),
            (">", numBoolBinop (>)),
            ("/=", numBoolBinop (/=)),
            (">=", numBoolBinop (>=)),
            ("<=", numBoolBinop (<=)),
            ("&&", boolBoolBinop (&&)),
            ("||", boolBoolBinop (||)),
            ("string=?", strBoolBinop (==)),
            ("string<?", strBoolBinop (<)),
            ("string>?", strBoolBinop (>)),
            ("string<=?", strBoolBinop (<=)),
            ("string>=?", strBoolBinop (>=)),
            ("car", car),
            ("cdr", cdr),
            ("cons", cons),
            ("eq?", eqv),
            ("eqv?", eqv),
            ("equal?", equal),
            ("string-length", stringLength),
            ("string-ref", stringRef),
            ("string", charsToString)
            ]

apply :: String -> [LispVal] -> ThrowsError LispVal
apply func args = maybe (throwError $ NotFunction "Unrecognized primitive function args" func)
    ($ args)
    (lookup func primitives)

clauseEval :: [LispVal] -> ThrowsError LispVal
clauseEval [] = throwError $ Default "No test is true" 
clauseEval ((List [test, expr]):remainingClauses) =
    case (eval test) of
        Left err -> throwError $ Default "Test clause could not be evaluated"
        Right testResult -> case testResult of  
            Bool True -> return . extractValue $ eval expr
            Bool False -> clauseEval remainingClauses

eval :: LispVal -> ThrowsError LispVal
eval val@(String _) = return val
eval val@(Number _) = return val
eval val@(Bool _) = return val
eval val@(Character _) = return val
eval (List [Atom "quote", val]) = return val
eval (List [Atom "if", pred, conseq, alt]) = 
     do result <- eval pred
        case result of 
             Bool True -> eval conseq
             Bool False  -> eval alt
             _ -> throwError $ TypeMismatch "Require a Bool" pred
eval (List ((Atom "cond"):clauses)) = clauseEval clauses
eval (List (Atom func : args)) = mapM eval args >>= apply func
eval val@(List _) = return val
eval badForm = throwError $ BadSpecialForm "Unrecognized special form " badForm

unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal

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


readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
    Left err -> throwError $ Parser err
    Right val -> return val

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

-- REPL stuff
flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

evalString :: String -> IO String
evalString expr = return $ extractValue $ trapError (liftM show $ readExpr expr >>= eval)

evalAndPrint :: String -> IO ()
evalAndPrint expr =  evalString expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
   result <- prompt
   if pred result 
      then return ()
      else action result >> until_ pred prompt action

runRepl :: IO ()
runRepl = until_ (== "quit") (readPrompt "Lisp>>> ") evalAndPrint

main :: IO ()
main = do args <- getArgs
          case length args of
               0 -> runRepl
               1 -> evalAndPrint $ args !! 0
               otherwise -> putStrLn "Program takes only 0 or 1 argument"