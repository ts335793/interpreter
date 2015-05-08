module Main where

import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )

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

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: Verbosity -> ParseFun Exp -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: Verbosity -> ParseFun Exp -> String -> IO ()
run v p s =
  let ts = myLexer s 
  in case p ts of
    Bad s -> do
      putStrLn "\nParse Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn s
    Ok tree -> do
      putStrLn "\nParse Successful!"
      showTree v tree
      putStrLn "\nRunning type checker..."
      print (runTypeOf tree)
      putStrLn "\nEvaluating program..."
      print (runEval tree)

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree = do
  putStrV v $ "\n[Abstract syntax]\n\n" ++ show tree
  putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> runFile 2 pExp f
    _ -> print "usage: runhaskell Main.hs source_file"
