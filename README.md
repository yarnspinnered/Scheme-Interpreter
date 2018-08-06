# Scheme-Interpreter
A limited scheme interpreter written in Haskell
This was done by closely following the guide at https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/

# Compilation
Install ghc with apt-get
sudo apt-get install cabal-install;cabal update;cabal install parsec
libghc6-mtl-dev <- might be required 
ghc --make -fglasgow-exts -o lisp Main.hs

# Overall structure
The parsing is primarily handled in LispParsing. The Parsec library is used to parse the tokens into Haskell values contained inside LispVals.

The listing of types is covered by LispTypes. Two major types are LispError (For returning errors) and LispVal (For all Lisp objects, including functions) types. At the REPL level, they are contained in a IOThrowsError monad, a monad combining Except and IO. But when processing values in primitive functions, they are contained in ThrowsError monad (An alias for Either LispError).

Basic Lisp functions such as (+) etc are contained in LispPrimitives. They work primarily with a list of lispvals before returning a throwsError lispVal in the case that there is an error.

The REPL loop works with the IOThrowsError monad. An Env (The set of name/value pairs, represented by IORef) is initialized with the primitive functions then it enters a forever running loop. Expressions are evaled and pattern matched. Special actions are taken for keywords such as "lambda" or "define" which modify the Env. In particular, a new Env is created by relying on writeIORef. For standard expressions, they are evaluated and printed to stdout.

