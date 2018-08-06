import Text.ParserCombinators.Parsec hiding (spaces)
import System.Environment
import Control.Monad
import Control.Monad.Error (runErrorT)
import Numeric 
import Data.Array
import Data.Typeable
import Data.IORef
import Control.Monad.Except
import System.IO

-- State stuff
type Env = IORef [(String, IORef LispVal)]

nullEnv :: IO Env
nullEnv = newIORef []

-- ExceptT is a monad transformer. Combine IO Monad with error handling monad
type IOThrowsError = ExceptT LispError IO

-- Haskell's inbuilt lifting lets us convert the lower IO monad into the combined monad
-- However, no lifting for converting the higher throwsError monad into combined monad, thus write it 
liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

-- Check if string exists in the state
-- Get state from envRef, get State from it, construct a maybe that is False if lookup fails and True otherwise. Lifti nto Bool
isBound :: Env -> String -> IO Bool
isBound envRef var = readIORef envRef >>= return . maybe False (const True) . lookup var

-- Get an existing variable
-- Turn IORef to IO monad. LiftIO turns this into a IOThrowsError monad containing a Env
-- Do a lookup with a maybe. Default value is unbound var, if succeeds, it reads the IORef then lifts it
getVar :: Env -> String -> IOThrowsError LispVal
getVar envRef var  =  do env <- liftIO $ readIORef envRef
                         maybe (throwError $ UnboundVar "Getting an unbound variable" var)
                               (liftIO . readIORef)
                               (lookup var env)

-- Edit an existing variable
-- WriteIORef expects a ref then value. Flip it since it gets the Ref as an argument. Lift the whole fn.
setVar :: Env -> String -> LispVal -> IOThrowsError LispVal
setVar envRef var value = do env <- liftIO $ readIORef envRef
                             maybe (throwError $ UnboundVar "Setting an unbound variable" var)
                                   (liftIO . (flip writeIORef value))
                                   (lookup var env)
                             return value

-- create a new var
-- Extract out whether already defined using isBound
-- If already defined, we can just use setVar
-- If not, create a new IORef using the new value. Get existing env. Add that key,value to env.
-- Lift whole thing in the end
defineVar :: Env -> String -> LispVal -> IOThrowsError LispVal
defineVar envRef var value = do
     alreadyDefined <- liftIO $ isBound envRef var
     if alreadyDefined
        then setVar envRef var value >> return value
        else liftIO $ do
             valueRef <- newIORef value
             env <- readIORef envRef
             writeIORef envRef ((var, valueRef) : env)
             return value             

-- Define multiple vars at once.
-- addBinding converts a (Key,Value) pair into a (Key, IORef Value) pair
-- extendEnv uses mapM to convert a list of key,value pairs into a list of (key, IORef value) pairs
-- This is then appended to the env and lifted 
bindVars :: Env -> [(String, LispVal)] -> IO Env
bindVars envRef bindings = readIORef envRef >>= extendEnv bindings >>= newIORef
     where extendEnv bindings env = liftM (++ env) (mapM addBinding bindings)
           addBinding (var, value) = do ref <- newIORef value
                                        return (var, ref)

-- trapError to convert action to a string before running whole computation with runErrorT.
-- result of that is passed to extractValue and returned within a IO monad
runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = runExceptT (trapError action) >>= return . extractValue

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
             | PrimitiveFunc ([LispVal] -> ThrowsError LispVal)
             | Func { params :: [String], vararg :: (Maybe String),
                    body :: [LispVal], closure :: Env }
            

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
showVal (PrimitiveFunc _) = "<primitive>"
showVal (Func {params = args, vararg = varargs, body = body, closure = env}) =
   "(lambda (" ++ unwords (map show args) ++
      (case varargs of
         Nothing -> ""
         Just arg -> " . " ++ arg) ++ ") ...)"

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

trapError :: IOThrowsError String -> IOThrowsError String
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
-- Helper functions
makeFunc varargs env params body = return $ Func (map showVal params) varargs body env
makeNormalFunc = makeFunc Nothing
makeVarArgs = makeFunc . Just . showVal

-- Bind primitive functions at startup, now no longer do a special lookup
primitiveBindings :: IO Env
primitiveBindings = nullEnv >>= (flip bindVars $ map makePrimitiveFunc primitives)
     where makePrimitiveFunc (var, func) = (var, PrimitiveFunc func)
-- Evaluating stuff
-- Represent functions as lispval and apply it to a list of args
-- Functions are either PrimitiveFunc or user-defined Func
-- Check argument count
-- If okay, zip them, add them to the env, lift it into IOThrowsError monad
-- After that, add in the varArgs and finally eval it by evaluating each expression in the body and lifting the last Lispval
apply :: LispVal -> [LispVal] -> IOThrowsError LispVal
apply (PrimitiveFunc func) args = liftThrows $ func args
apply (Func params varargs body closure) args =
      if num params /= num args && varargs == Nothing
         then throwError $ NumArgs (num params) args
         else (liftIO $ bindVars closure $ zip params args) >>= bindVarArgs varargs >>= evalBody
      where remainingArgs = drop (length params) args
            num = toInteger . length
            evalBody env = liftM last $ mapM (eval env) body
            bindVarArgs arg env = case arg of
                Just argName -> liftIO $ bindVars env [(argName, List $ remainingArgs)]
                Nothing -> return env

clauseEval :: Env -> [LispVal] -> IOThrowsError LispVal
clauseEval env [] = throwError $ Default "No test is true" 
clauseEval env ((List [test, expr]):remainingClauses) = do
    evaluationRes <- eval env test
    case evaluationRes of
        Bool True -> do
            expr_evaled <- eval env expr
            return expr_evaled
        Bool False -> clauseEval env remainingClauses
        _ -> throwError $ Default "Test expr could not be evaled"     
    -- case evaluationRes of
    --     Left err -> throwError $ Default "Test clause could not be evaluated"
    --     Right testResult -> case testResult of  
    --         Bool True -> return . extractValue $ eval env expr
    --         Bool False -> clauseEval env remainingClauses

eval :: Env -> LispVal -> IOThrowsError LispVal
eval env val@(String _) = return val
eval env val@(Number _) = return val
eval env val@(Bool _) = return val
eval env val@(Character _) = return val
eval env (List [Atom "quote", val]) = return val
eval env (List [Atom "if", pred, conseq, alt]) = 
     do result <- eval env pred
        case result of 
             Bool True -> eval env conseq
             Bool False  -> eval env alt
             _ -> throwError $ TypeMismatch "Require a Bool" pred
eval env (List [Atom "set!", Atom var, form]) =
    eval env form >>= setVar env var
eval env (List (Atom "define" : List (Atom var : params) : body)) =
     makeNormalFunc env params body >>= defineVar env var
eval env (List (Atom "define" : DottedList (Atom var : params) varargs : body)) =
     makeVarArgs varargs env params body >>= defineVar env var
eval env (List (Atom "lambda" : List params : body)) =
     makeNormalFunc env params body
eval env (List (Atom "lambda" : DottedList params varargs : body)) =
     makeVarArgs varargs env params body
eval env (List (Atom "lambda" : varargs@(Atom _) : body)) =
     makeVarArgs varargs env [] body
eval env (List ((Atom "cond"):clauses)) = clauseEval env clauses
eval env (List (function : args)) = do
     func <- eval env function
     argVals <- mapM (eval env) args
     apply func argVals
eval env val@(List _) = return val
eval env (Atom id) = getVar env id
eval env badForm = throwError $ BadSpecialForm "Unrecognized special form " badForm

     
-- Parsing stuff
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

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ (liftThrows $ readExpr expr) >>= eval env

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr =  evalString env expr >>= putStrLn

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
   result <- prompt
   if pred result 
      then return ()
      else action result >> until_ pred prompt action

runOne :: String -> IO ()
runOne expr = primitiveBindings >>= flip evalAndPrint expr

runRepl :: IO ()
runRepl = primitiveBindings >>= until_ (== "quit") (readPrompt "Lisp>>> ") . evalAndPrint

main :: IO ()
main = do args <- getArgs
          case length args of
               0 -> runRepl
               1 -> runOne $ args !! 0
               otherwise -> putStrLn "Program takes only 0 or 1 argument"