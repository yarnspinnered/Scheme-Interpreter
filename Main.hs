import Text.ParserCombinators.Parsec (parse)
import Control.Monad (liftM)
import Control.Monad.Except (runExceptT, liftIO, throwError, catchError)
import Data.Array
import Data.Typeable
import Data.IORef
import System.Environment
import System.IO

-- My stuff
import LispParsing
import LispTypes
import LispPrimitives

nullEnv :: IO Env
nullEnv = newIORef []
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

trapError :: IOThrowsError String -> IOThrowsError String
trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

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
eval env (List [Atom "define", Atom var, form]) =
     eval env form >>= defineVar env var
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

readExpr :: String -> ThrowsError LispVal
readExpr input = case parse parseExpr "lisp" input of
    Left err -> throwError $ Parser err
    Right val -> return val

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