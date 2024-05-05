-----------------
-- TOKEN TREES --
-----------------

-- Token trees are a data structure (inspired by the Rust compiler) that is
-- similar to a list of tokens, as produced by a classical lexer, but with one
-- change: tokens within matching symbols (parentheses, curly braces) are
-- turned into `Group` tokens. A lexed program has the shape of a tree of
-- tokens, thus the name. This approach turns out to make parsing easier in
-- various cases.

module Spreadsheet.Tokens
  ( TokenStream,
    TokenTree (..),
    KeywordKind (..),
    LiteralKind (..),
    ttpos,
    tterr,
  )
where

import Spreadsheet.Utils

-- A token stream is a list of token trees. The top-level lexer will output
-- instances of this type.
type TokenStream =
  [TokenTree]

-- The token tree definition itself.
data TokenTree
  = Keyword (Int, Int) KeywordKind -- keyword, reserved by the language
  | Literal (Int, Int) LiteralKind -- constant value
  | Ident (Int, Int) String -- non-keyword, non-constant identifier
  | Operator (Int, Int) String -- binary operator or other punctuation
  | Group (Int, Int) Char TokenStream -- matched group; the second component
  --   is either '(' or '{'
  deriving (Show)

data KeywordKind
  = KComment String
  | KConst
  | KInput
  | KProgram
  | KIterated
  | KEnsures
  | KTransparent
  | KResult
  | KReturn
  | KVar
  | KIf
  | KElif
  | KElse
  | KCell
  | KRange
  | KAssert
  | KBool
  | KInt
  deriving (Show)

data LiteralKind
  = LBool Bool
  | LInt Int
  deriving (Show)

-- Get the position of any token tree.
ttpos :: TokenTree -> (Int, Int)
ttpos (Ident p _) = p
ttpos (Keyword p _) = p
ttpos (Literal p _) = p
ttpos (Operator p _) = p
ttpos (Group p _ _) = p

-- Error reporting at the particular token.
tterr tt msg = err (ttpos tt) msg
