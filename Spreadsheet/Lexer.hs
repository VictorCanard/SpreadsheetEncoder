{-# LANGUAGE ViewPatterns #-}

-----------
-- LEXER --
-----------

-- Here we define a lexer for spreadsheets. It splits a source file into a grid
-- (that is, list of lists) of token streams (see `Tokens.hs`), which will later
-- be processed by the parser.

module Spreadsheet.Lexer
  ( lexexpr,
    lexprogram,
    Spreadsheet.Lexer.lex,
  )
where

import Data.Char
import Data.List
import Spreadsheet.Tokens
import Spreadsheet.Utils

-- The lexer itself. It starts the helper `s` with the correct initial state.
lex :: String -> [[TokenStream]]
lex src = s (1, 0) [] [] src

lexexpr :: String -> TokenStream
lexexpr src = res
  where
    (res, "", _) = h (1, 0) ',' src

lexprogram :: String -> TokenStream
lexprogram src = (Keyword (1, 0) KProgram) : res
  where
    (res, ",", _) = h (1, 0) ',' ("{" ++ src ++ "},")

-- `tok` prepends a token to the result of a recursive call to the helper.
tok :: TokenTree -> (TokenStream, String, (Int, Int)) -> (TokenStream, String, (Int, Int))
tok t (stream, src, p) = (t : stream, src, p)

-- Identifiers consist of alphanumerics and underscores.
isIdent c = isAlphaNum c || c == '_'

-- When matching keywords, we need to find them as a prefix, but also make sure
-- that the characters which immediately follow are not identifier characters.
-- This way, `if_` is not matched as the `if` keyword, but `if{` is.
kwd k src
  | k == src = Just []
  | isPrefixOf k src && not (isIdent c) = Just rest
  | otherwise = Nothing
  where
    rest@(c : _) = drop (length k) src

-- The top-level (spreadsheet) lexer helper. This matches on the structure of
-- the spreadsheet overall, to put cells into rows and columns. Cell types are
-- matched here (see `cell types` below), but cell contents are delegated to
-- the other lexer helper, `h`.
--   arguments:
--     current line/column position, for error reporting
--     current row tokens
--     current column tokens
--     string yet to be lexed
--   returns:
--     grid of lexed cells
s :: (Int, Int) -> [TokenStream] -> TokenStream -> String -> [[TokenStream]]
-- The lexing rules themselves.
--   whitespace and column/row ends
s (l, c) sr sc ('\n' : rest) = (sc : sr) : (s (l + 1, 0) [] [] rest)
s (l, c) sr sc ((isSpace -> True) : rest) = s (l, c + 1) sr sc rest
s (l, c) sr sc (',' : rest) = col sc (s (l, c + 1) sr [] rest)
  where
    col c (r : rs) = (c : r) : rs
--   comment cells
s (l, c) sr [] (kwd "comment" -> Just rest) = s (l, c + 7 + nlen) sr [Keyword (l, c) (KComment str)] srest
  where
    str = takeWhile (\v -> v /= '\n' && v /= ',') rest
    nlen = length str
    srest = drop nlen rest
--   cell types
s (l, c) sr [] (kwd "const" -> Just rest) = s (hl, hc) sr ((Keyword (l, c) KConst) : htok) hrest
  where
    (htok, hrest, (hl, hc)) = h (l, c + 5) ',' rest
s (l, c) sr [] (kwd "input" -> Just rest) = s (hl, hc) sr ((Keyword (l, c) KInput) : htok) hrest
  where
    (htok, hrest, (hl, hc)) = h (l, c + 5) ',' rest
s (l, c) sr [] (kwd "program" -> Just rest) = s (hl, hc) sr ((Keyword (l, c) KProgram) : htok) hrest
  where
    (htok, hrest, (hl, hc)) = h (l, c + 7) ',' rest
s (l, c) sr [] (kwd "row" -> Just rest) = s (hl, hc) sr ((Keyword (l, c) KIterated) : htok) hrest -- EXTENSION: ITERATED
  where
    (htok, hrest, (hl, hc)) = h (l, c + 3) ',' rest
s p sr sc "" = [sc : sr]
--   failure
s p _ [] rest = err p "unexpected (expecting column type)"
s p _ _ rest = err p "unexpected (expecting comma or new line)"

-- Valid single-character operators.
isOp1 :: Char -> Bool
isOp1 ':' = True
isOp1 '+' = True
isOp1 '-' = True
isOp1 '*' = True
isOp1 '/' = True
isOp1 '%' = True
isOp1 ',' = True
isOp1 '!' = True
isOp1 '<' = True
isOp1 '>' = True
isOp1 _ = False

-- Valid two-character operators.
isOp2 :: String -> Bool
isOp2 ":=" = True
isOp2 "!=" = True
isOp2 "==" = True
isOp2 "&&" = True
isOp2 "||" = True
isOp2 "<=" = True
isOp2 ">=" = True
isOp2 "=>" = True -- implication
isOp2 _ = False

-- The program lexer helper.
--   arguments:
--     current line/column position, for error reporting
--     which group are we looking to terminate
--     string yet to be lexed
--   returns:
--     lexed tokens
--     the rest of the string, if we found the group terminator
--     position at the end (EOF or end of current group)
h :: (Int, Int) -> Char -> String -> (TokenStream, String, (Int, Int))
-- The lexing rules themselves.
--   column or row end
h (l, c) ',' rest@(',' : _) = ([], rest, (l, c))
h (l, c) ',' rest@('\n' : _) = ([], rest, (l, c))
h (l, c) ',' "" = ([], "", (l, c))
--   whitespace
h (l, c) g ('\n' : rest) = h (l + 1, 0) g rest
h (l, c) g ((isSpace -> True) : rest) = h (l, c + 1) g rest
--   line comments
h (l, c) g ('/' : '/' : rest) = h (l, c + clen) g (drop clen rest)
  where
    clen = length (takeWhile (/= '\n') rest)
--   keywords
h (l, c) g (kwd "ensures" -> Just rest) = tok (Keyword (l, c) KEnsures) (h (l, c + 7) g rest)
h (l, c) g (kwd "transparent" -> Just rest) = tok (Keyword (l, c) KTransparent) (h (l, c + 11) g rest)
h (l, c) g (kwd "result" -> Just rest) = tok (Keyword (l, c) KResult) (h (l, c + 6) g rest)
h (l, c) g (kwd "var" -> Just rest) = tok (Keyword (l, c) KVar) (h (l, c + 3) g rest)
h (l, c) g (kwd "if" -> Just rest) = tok (Keyword (l, c) KIf) (h (l, c + 2) g rest)
h (l, c) g (kwd "elif" -> Just rest) = tok (Keyword (l, c) KElif) (h (l, c + 4) g rest)
h (l, c) g (kwd "else" -> Just rest) = tok (Keyword (l, c) KElse) (h (l, c + 4) g rest)
h (l, c) g (kwd "cell" -> Just rest) = tok (Keyword (l, c) KCell) (h (l, c + 4) g rest)
h (l, c) g (kwd "range" -> Just rest) = tok (Keyword (l, c) KRange) (h (l, c + 5) g rest)
h (l, c) g (kwd "assert" -> Just rest) = tok (Keyword (l, c) KAssert) (h (l, c + 6) g rest)
h (l, c) g (kwd "return" -> Just rest) = tok (Keyword (l, c) KReturn) (h (l, c + 6) g rest)
h (l, c) g (kwd "Bool" -> Just rest) = tok (Keyword (l, c) KBool) (h (l, c + 4) g rest)
h (l, c) g (kwd "Int" -> Just rest) = tok (Keyword (l, c) KInt) (h (l, c + 3) g rest)
--   literals
h (l, c) g (kwd "true" -> Just rest) = tok (Literal (l, c) (LBool True)) (h (l, c + 4) g rest)
h (l, c) g (kwd "false" -> Just rest) = tok (Literal (l, c) (LBool False)) (h (l, c + 5) g rest)
h (l, c) g src@(takeWhile isDigit -> num@(_ : _)) = tok (Literal (l, c) (LInt (read num))) (h (l, c + nlen) g (check (drop nlen src)))
  where
    nlen = length num
    check [] = []
    check src@((isSpace -> True) : rest) = src
    check src@((isAlphaNum -> True) : rest) = err (l, c + nlen) "unexpected characters after number literal"
    check src = src
--   operators
h (l, c) g (op1 : op2 : rest)
  | isOp2 op = tok (Operator (l, c) op) (h (l, c + 2) g rest)
  where
    op = [op1, op2]
h (l, c) g (op : rest)
  | isOp1 op = tok (Operator (l, c) [op]) (h (l, c + 1) g rest)
--   identifiers
h (l, c) g src@(takeWhile isIdent -> ident@(_ : _)) =
      tok (Ident (l, c) ident) (h (l, c + (length ident)) g (drop (length ident) src))
--   group start
h (l, c) g ('{' : rest) = tok (Group (l, c) '{' sub) (h (sl, sc) g srest)
  where
    (sub, srest, (sl, sc)) = h (l, c + 1) '{' rest
h (l, c) g ('(' : rest) = tok (Group (l, c) '(' sub) (h (sl, sc) g srest)
  where
    (sub, srest, (sl, sc)) = h (l, c + 1) '(' rest
--   group end
h (l, c) '{' ('}' : rest) = ([], rest, (l, c + 1))
h (l, c) '(' (')' : rest) = ([], rest, (l, c + 1))
--   failure
h p _ ('}' : rest) = err p "unexpected right curly"
h p _ (')' : rest) = err p "unexpected right paren"
h p _ _ = err p "unexpected token"
