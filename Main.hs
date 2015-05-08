module Main where

import System.IO
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

runFile :: ParseFun Exp -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun Exp -> String -> IO ()
run p s =
  let ts = myLexer s 
  in case p ts of
    Bad s -> do
      hPutStrLn stderr "Parse Failed..."
      hPutStrLn stderr s
    Ok tree ->
      case runTypeOf tree of
        Right t ->
          case runEval tree of
            Right v -> do
              print v
              hPutStrLn stderr (show t)
            Left msg -> do
              hPutStrLn stderr "Run time error..."
              hPutStrLn stderr msg
        Left msg -> do
          hPutStrLn stderr "Type interference error..."
          hPutStrLn stderr msg

main :: IO ()
main = do
  args <- getArgs
  case args of
    [f] -> runFile pExp f
    _ -> hPutStrLn stderr "usage: runhaskell Main.hs source_file"

