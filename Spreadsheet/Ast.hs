--------------------
-- AST DEFINITION --
--------------------

-- Here we define the abstract syntax tree (AST) for spreadsheets. Instances of
-- such ASTs are created by the `Parser.parse` function.

module Spreadsheet.Ast
  ( Spreadsheet,
    Cell (..),
    Type (..),
    VarDecl,
    CellPos,
    Expr (..),
    Code,
    Stmt (..),
  )
where

-- A spreadsheet.
type Spreadsheet = [[Cell]]

-- A cell.
data Cell
  = CEmpty -- empty cell or comment cell
  | CConst Int
  | CInput Type (Maybe Expr)
  | CInputBool (Maybe Expr)
  | CProgram 
      { 
        retType :: Type,
        -- The code of the program cell.
        code :: Code,
        -- Postcondition, if any.
        post :: Maybe Expr,
        -- Is the cell marked transparent?
        transparent :: Bool
      }
  | CIterated [Expr]
  deriving (Eq, Show)

-- Primitive types.
data Type = Int | Bool
  deriving (Eq, Show)

-- Variable declaration.
-- Example (syntax):
--   var x: Int
-- Example (parsed):
--   ("x", Int)
type VarDecl = (String, Type)

type CellPos = (Int, Int)

-- Expressions. Should not have side effects!
data Expr
  = EConstBool Bool -- true, false
  | EConstInt Int -- integer constant
  | EVar String -- global or local variable
  | EParens Expr -- expression grouped in parentheses
  | EUnaryOp String Expr -- unary operation
  | EBinaryOp Expr String Expr -- binary operation
  | ECell CellPos
  | ECall String [Expr]
  | ERange CellPos CellPos
  deriving (Eq, Show)

-- Statements and code blocks.
type Code = [Stmt]

data Stmt
  = Skip -- no-op
  | Assign String Expr -- assignment to variable
  | Cond Expr Code Code -- conditional; note that `elif` is represented as
  --   another conditional in the `else` branch
  | Nondet Code Code -- non-deterministic choice (not used in this project!)
  | Assert Expr -- assertion
  | Local String Type (Maybe Expr) -- local variable declaration
  | Return Expr
  deriving (Eq, Show)
