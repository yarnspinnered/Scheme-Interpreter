module LispPrimitives where
import Control.Monad (liftM)
import Control.Monad.Except (throwError, catchError)

-- my stuff
import LispTypes

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


unpackEquals :: LispVal -> LispVal -> Unpacker -> ThrowsError Bool
unpackEquals arg1 arg2 (AnyUnpacker unpacker) = 
             do unpacked1 <- unpacker arg1
                unpacked2 <- unpacker arg2
                return $ unpacked1 == unpacked2
        `catchError` (const $ return False)

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