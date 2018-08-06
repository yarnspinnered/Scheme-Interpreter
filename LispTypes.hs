module LispTypes where
import Control.Monad.Except (ExceptT, liftIO, throwError, catchError)
import Text.ParserCombinators.Parsec (ParseError)
import Data.IORef
import Data.Array

-- State stuff
type Env = IORef [(String, IORef LispVal)]

-- ExceptT is a monad transformer. Combine IO Monad with error handling monad
type IOThrowsError = ExceptT LispError IO

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

-- -fglasgow-exts Allows for existential types. i.e. lists that contain different types as long as they belong to same type-class
-- Defined on any type that is an instance of the Eq typeClass. Unpacker takes one function (that maps from LispVal to that specific type)
data Unpacker = forall a. Eq a => AnyUnpacker (LispVal -> ThrowsError a)

unwordsList :: [LispVal] -> String
unwordsList = unwords . map showVal