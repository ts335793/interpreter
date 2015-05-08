module Main where

import System.Environment (getArgs)

import BNFC.LexLanguage
import BNFC.ParLanguage
import BNFC.SkelLanguage
import BNFC.PrintLanguage
import BNFC.AbsLanguage
import BNFC.ErrM

import Evaluator
import TypeInterference

type ParseFun a = [Token] -> Err a

type Verbosity = Int


runFile :: ParseFun Exp -> FilePath -> IO ()
runFile p f = putStrLn f >> readFile f >>= run p

run :: ParseFun Exp -> String -> IO ()
run p s =
  let ts = myLexer s 
  in case p ts of
    Bad s -> do
      putStrLn "\nParse Failed...\n"
      putStrLn "Tokens:"
      print ts
      putStrLn s
    Ok tree -> do
      putStrLn "\nParse Successful!"
      showTree tree
      putStrLn "\nRunning type checker..."
      print (runTypeOf tree)
      putStrLn "\nEvaluating program..."
      print (runEval tree)

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> runFile pExp f
    _ -> print "usage: runhaskell Main.hs source_file"

