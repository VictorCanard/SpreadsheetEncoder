----------------
-- ENTRYPOINT --
----------------

-- This module defines the main function of the spreadsheet project.
-- It supports the following commands:
--
--   ./Project.o lex <input.spr>
--     Lexes the given spreadsheet and outputs the token stream.
--
--   ./Project.o parse <input.spr>
--     Parses the given spreadsheet and outputs the AST.
--
--   ./Project.o run <input.spr> <cell=value>
--     Interprets the given spreadsheet and outputs the resulting cell values.
--
--   ./Project.o encode-expr "<expression>"
--     Encodes the given expression and prints out the result. Note that the
--     expression must be a single argument passed to the program, so it will
--     probably need to be enclosed in quotes in the terminal. This will invoke
--     the `encodeexpr` function from `Encoder/Encoder.hs`, which is not
--     implemented in the skeleton files (required task 1).
--
--   ./Project.o encode-program <input.spr> <output.vpr>
--     Encodes the given program and writes the Viper code to the output path.
--     This assumes that the input path contains *only* the code of a program
--     cell. This will invoke the `encodeprogram` function from
--     `Encoder/Encoder.hs`, which is not implemented in the skeleton files
--     (required task 2).
--
--   ./Project.o encode <input.spr> <output.vpr>
--     Encodes the given spreadsheet and writes the Viper code to the output
--     path. This will invoke the `encode` function from `Encoder/Encoder.hs`,
--     which is not implemented in the skeleton files (required tasks 3 and 4).

module Main where

import Data.Time
import System.Environment
import System.Exit
import System.IO

import Encoder.Encoder (encodeexpr, encodeprogram, encode)
import Spreadsheet.Lexer (lexexpr, lexprogram, lex)
import Spreadsheet.Parser (pexprfull, pcell, psheet)
import Interp.Interp (esheet)
import Interp.Printer (showsheet)
import Viper.Printer (renderVExpr, renderVMember, renderVProgram)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["lex", path] -> do
      contents <- readFile path
      print (Spreadsheet.Lexer.lex contents)
    ["parse", path] -> do
      contents <- readFile path
      print (psheet (Spreadsheet.Lexer.lex contents))
    ("run" : path : cellspec) -> do
      contents <- readFile path
      UTCTime _ time <- getCurrentTime
      let sheet = psheet (Spreadsheet.Lexer.lex contents)
      putStrLn (showsheet (esheet (truncate time) sheet cellspec))
    ["encode-expr", input] -> do
      let expr = pexprfull (lexexpr input)
      let viper = encodeexpr expr
      putStrLn (renderVExpr viper)
    ["encode-program", input, output] -> do
      contents <- readFile input
      let program = pcell (lexprogram contents)
      let viper = encodeprogram program
      writeFile output (renderVMember viper)
    ["encode", input, output] -> do
      contents <- readFile input
      let sheet = psheet (Spreadsheet.Lexer.lex contents)
      let viper = encode sheet
      writeFile output (renderVProgram viper)
    _ -> do
      name <- getProgName
      hPutStrLn stderr $ ("usage:\n"
        ++ "  " ++ name ++ " lex <input.spr>\n"
        ++ "  " ++ name ++ " parse <input.spr>\n"
        ++ "  " ++ name ++ " run <input.spr> <cell=value> ...\n"
        ++ "  " ++ name ++ " encode-expr \"<expression>\"\n"
        ++ "  " ++ name ++ " encode-program <input.spr> <output.vpr>\n"
        ++ "  " ++ name ++ " encode <input.spr> <output.vpr>\n")
      exitFailure
