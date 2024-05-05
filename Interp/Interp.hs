{-# LANGUAGE ViewPatterns #-}

-----------------
-- INTERPRETER --
-----------------

module Interp.Interp (
  esheet,
  RunValue (..),
) where

import Data.Int (Int32)
import Data.Bits
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Text.Read (readMaybe)

import Spreadsheet.Ast
import Spreadsheet.Parser (pcellpos)

-- To provide some non-determinism, we use a pseudo-random number generator
-- (PRNG), which is seeded by the time at which the interpreter is invoked.
-- Note that the non-deterministic choice has been removed from this project!
prng :: Int32 -> (Int32, Int)
prng a = (d, fromIntegral a)
  where
    b = a `xor` (shiftL a 13)
    c = b `xor` (shiftR b 17)
    d = c `xor` (shiftL c  5)

-- Runtime representations:
--   Value, as stored in a variable.
data RunValue =
    RVBool Bool
  | RVInt Int
  | RVRange CellPos CellPos
  deriving (Eq, Show)
--   Variable mapping, from variable names to runtime values.
type RunVars = M.Map String RunValue
--   Runtime state.
data RunState = RunState {
  -- Local variables in scope.
  store :: RunVars,
  -- PRNG seed.
  seed  :: Int32,
  -- The entire spreadsheet, for cell references.
  sheet :: Spreadsheet,
  -- The call stack, to detect cyclic references.
  stack :: [CellPos],
  -- User inputs.
  input :: M.Map CellPos Int
} deriving (Eq, Show)
--   Execution result, obtained by executing a code block. Consists of the
--   updated global variables and the updated PRNG seed.
data RunResult =
    RRReturn RunValue
  | RRExit (RunVars, Int32)
  | RRUpdate (RunVars, Int32)
  | RRNoop

-- Execute a binary operation on two integer arguments.
binopInt :: String -> Maybe (Int -> Int -> RunValue)
binopInt "%"  = Just (\l -> \r -> RVInt (mod l r))
binopInt "*"  = Just (\l -> \r -> RVInt (l * r))
binopInt "/"  = Just (\l -> \r -> RVInt (div l r))
binopInt "+"  = Just (\l -> \r -> RVInt (l + r))
binopInt "-"  = Just (\l -> \r -> RVInt (l - r))
binopInt "<=" = Just (\l -> \r -> RVBool (l <= r))
binopInt "<"  = Just (\l -> \r -> RVBool (l < r))
binopInt ">=" = Just (\l -> \r -> RVBool (l >= r))
binopInt ">"  = Just (\l -> \r -> RVBool (l > r))
binopInt "==" = Just (\l -> \r -> RVBool (l == r))
binopInt "!=" = Just (\l -> \r -> RVBool (l /= r))
binopInt _    = Nothing

-- Execute a binary operation on two Boolean arguments.
binopBool :: String -> Maybe (Bool -> Bool -> RunValue)
binopBool "&&" = Just (\l -> \r -> RVBool (l && r))
binopBool "||" = Just (\l -> \r -> RVBool (l || r))
binopBool "==" = Just (\l -> \r -> RVBool (l == r))
binopBool "!=" = Just (\l -> \r -> RVBool (l /= r))
binopBool _    = Nothing

-- Extract a Boolean from a runtime value, or fail.
ebool :: RunValue -> Bool
ebool (RVBool v) = v
ebool _ = error "expected Boolean value"

eint :: RunValue -> Int
eint (RVInt v) = v
eint _ = error "expected integer value"

-- Evaluate an expression given a store.
eexpr :: RunState -> Expr -> RunValue
--   constants
eexpr _ (EConstBool v) = RVBool v
eexpr _ (EConstInt v)  = RVInt v
--   variables and handler arguments
eexpr s (EVar name) = fromMaybe (error ("no such variable " ++ name)) (M.lookup name (store s))
--   groups
eexpr s (EParens e) = eexpr s e
--   unary operations
eexpr s (EUnaryOp "-" (eexpr s -> RVInt v)) = RVInt (-v)
eexpr s (EUnaryOp "!" (eexpr s -> RVBool v)) = RVBool (not v)
eexpr s (EUnaryOp op _) = error ("invalid unary operation " ++ op)
--   binary operations
eexpr s (EBinaryOp (eexpr s -> RVInt l) (binopInt -> Just op) (eexpr s -> RVInt r)) = op l r
eexpr s (EBinaryOp (eexpr s -> RVBool l) (binopBool -> Just op) (eexpr s -> RVBool r)) = op l r
eexpr s (EBinaryOp _ op _) = error ("invalid binary operation " ++ op)
--   cell references
eexpr s (ECell pos) = RVInt (ecell s pos)
eexpr s (ERange pos1 pos2) = RVRange pos1 pos2
--   aggregation
eexpr s (ECall "sum" [(eexpr s -> RVRange pos1 pos2)]) = RVInt (aggregate s pos1 pos2 0 (+))
eexpr s (ECall "product" [(eexpr s -> RVRange pos1 pos2)]) = RVInt (aggregate s pos1 pos2 1 (*))
eexpr s (ECall "operate" [(eexpr s -> RVRange pos1 pos2), (eexpr s -> RVInt acc), op]) = RVInt (aggregate s pos1 pos2 acc f)
  where f xv yv = eint (eexpr (s { store = M.insert "x" (RVInt xv) (M.insert "y" (RVInt yv) (store s)) }) op)
--   failure
eexpr _ e = error ("invalid expression: " ++ (show e))

aggregate :: RunState -> CellPos -> CellPos -> Int -> (Int -> Int -> Int) -> Int
aggregate s (colstart, rowstart) (colend, rowend) acc f
  | rowstart > rowend = acc
  | otherwise         = aggregate s (colstart, rowstart + 1) (colend, rowend) (aggrow s (colstart, rowstart) colend acc f) f

aggrow :: RunState -> CellPos -> Int -> Int -> (Int -> Int -> Int) -> Int
aggrow s pos@(col, row) colend acc f
  | col > colend = acc
  | otherwise    = aggrow s (col + 1, row) colend (f acc (ecell s pos)) f

-- Evaluate a statement given a store and a PRNG seed.
estmt :: RunState -> Stmt -> RunResult
--   skip
--estmt (globals, _) seed Skip = (globals, seed)
--   assignment
estmt s (Assign name e)
  -- | M.member name (consts)  = error ("cannot reassign constant " ++ name)
  | M.member name rstore = RRUpdate (M.insert name (eexpr s e) rstore, seed s)
  | otherwise            = error ("no such variable " ++ name)
  where rstore = store s
--   conditional
estmt s (Cond (eexpr s -> v) codeIf codeElse) = case (ecode s (if (ebool v) then codeIf else codeElse)) of
  RRExit (g, ns) -> RRUpdate (g, ns)
  v -> v
--   non-deterministic conditional
estmt s (Nondet codeIf codeElse) =
  ecode (s { seed = nseed }) (if ((mod select 2) == 0) then codeIf else codeElse)
  where (nseed, select) = prng (seed s)
--   assertion
estmt s (Assert e) = if (ebool (eexpr s e))
  then RRNoop
  else error ("assertion failed: " ++ (show e))
--   local variable declaration
estmt s (Local name ty e) =
  RRUpdate (M.insert name (fromMaybe (initval ty) (fmap (eexpr s) e)) (store s), seed s)
--   return
estmt s (Return e) = RRReturn (eexpr s e)

estmt _ stmt = error ("statement: " ++ (show stmt))

-- Evaluate a code block given a store and a PRNG seed.
ecode :: RunState -> Code -> RunResult
ecode s [] = RRExit (store s, seed s)
ecode s (stmt : rest) = case (estmt s stmt) of
  RRExit u -> RRExit u
  RRReturn v -> RRReturn v
  RRUpdate (nstore, nseed) -> ecode (s { store = nstore, seed = nseed }) rest
  RRNoop -> ecode s rest

exitval :: RunResult -> Int
exitval (RRExit _) = 0 -- error?
exitval (RRReturn (RVInt v)) = v
exitval (RRReturn (RVBool _)) = error "unexpected Boolean return"
exitval (RRUpdate _) = error "unexpected run result"
exitval RRNoop = error "unexpected run result"

-- Provide a default value for the given type.
initval :: Type -> RunValue
initval Int  = RVInt 0
initval Bool = RVBool False

ecell :: RunState -> CellPos -> Int
ecell s pos@(cc, cr)
  | elem pos (stack s) = error ("cell cycle: " ++ (show (stack s)))
  | cr >= (length (sheet s)) = error "reference out of bounds"
  | cc >= (length (sheet s !! cr)) = error "reference out of bounds"
  | otherwise = case (sheet s !! cr !! cc) of
    CEmpty -> 0
    CConst v -> v
    CInput t pre -> if check
      then val
      else error ("user input breaks precondition: " ++ (show pos))
      where
        val = fromMaybe (error ("user input missing: " ++ (show pos))) (M.lookup pos (input s))
        check = maybe True (\e -> ebool (eexpr (cs { store = M.singleton "value" (RVInt val), sheet = [] }) e)) pre
    CProgram t code post transparent -> if check
      then val
      else error ("program cell breaks postcondition: " ++ (show pos))
      where
        val = exitval (ecode cs code)
        check = maybe True (\e -> ebool (eexpr (cs { store = M.singleton "value" (RVInt val) }) e)) post
  where cs = s { stack = pos : (stack s) }

esheet :: Int32 -> Spreadsheet -> [String] -> [[Int]]
esheet seed sheet spec =
  map (\(cr, row) -> map (\(cc, _) -> ecell (RunState (M.empty) seed sheet [] input) (cc, cr)) (zip [0..] row)) (zip [0..] sheet)
  where
    input = M.fromList (map ppair spec)
    ppair :: String -> (CellPos, Int)
    ppair s = (pcellpos (takeWhile (/= '=') s), fromMaybe (error "invalid cell value") (readMaybe (drop 1 (dropWhile (/= '=') s))))
