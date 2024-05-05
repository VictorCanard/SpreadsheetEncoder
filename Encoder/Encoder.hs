module Encoder.Encoder
  ( encodeexpr,
    encodeprogram,
    encode,
  )
where

import Data.Char

import Spreadsheet.Ast
import Spreadsheet.Utils
import Viper.Ast

-- Helper functions to go from a cell pos to its string representation and back
posToString :: CellPos -> String
posToString cellPos = chr (ord 'A' + fst cellPos) : show (snd cellPos + 1)

stringToPos :: String -> CellPos
stringToPos (letter : num) = (digitToInt (head num) - 1, ord letter - ord 'A')
--

-- Ranges for aggregated operations.
type Range = [CellPos]

makeRange :: CellPos -> CellPos -> Range
makeRange (start_col, start_row) (end_col, end_row)
  | start_col == end_col = map (start_col,) [start_row .. end_row] -- iterates over rows
  | start_row == end_row = map (,start_row) [start_col .. end_col]
  | otherwise = []

replaceXInArg :: Expr -> Expr -> Expr
replaceXInArg e1 = replaceInOp e1 (0, 0)

replaceInOp :: Expr -> CellPos -> Expr -> Expr
replaceInOp acc cp (EVar s)
  | s == "x" = acc
  | s == "y" = ECell cp
  | otherwise = undefined
replaceInOp acc cp (EParens e) = replaceInOp acc cp e
replaceInOp acc cp (EUnaryOp op e) = EUnaryOp op (replaceInOp acc cp e) -- Could happen if we extend aggregation operations to booleans.
replaceInOp acc cp (EBinaryOp e1 op e2) = EBinaryOp (replaceInOp acc cp e1) op (replaceInOp acc cp e2)
replaceInOp acc cp expr = expr

-- We represent everything quite straightforwardly, and we make cells variables that have the name corresponding to their position.
encodeexpr :: Expr -> VExpr
encodeexpr (EConstBool b) = if b then VTrueLit else VFalseLit
encodeexpr (EConstInt i) = VIntLit (toInteger i)
encodeexpr (EVar s) = VVar s
encodeexpr (EParens e) = encodeexpr e
encodeexpr (EUnaryOp op e) = VUnaryOp op (encodeexpr e)
encodeexpr (EBinaryOp e1 op e2) = VBinaryOp (encodeexpr e1) op (encodeexpr e2)
encodeexpr (ECell cellPos) =
  encodeexpr
    ( EVar
        (posToString cellPos)
    )
encodeexpr (ECall func_name args) =
  case func_name of
    "sum" ->
      let (ERange start_cp end_cp) = head args
       in let range = makeRange start_cp end_cp
           in encodeexpr (foldl (\expr cp -> EBinaryOp expr "+" (ECell cp)) (EConstInt 0) range)
    "product" ->
      let (ERange start_cp end_cp) = head args
       in let range = makeRange start_cp end_cp
           in encodeexpr (foldl (\expr cp -> EBinaryOp expr "*" (ECell cp)) (EConstInt 1) range)
    "operate" ->
      let [ERange start_cp end_cp, def_val, op] = take 3 args
       in let range = makeRange start_cp end_cp
           in encodeexpr (foldl (\acc cp -> replaceInOp acc cp op) def_val range)
encodeexpr expr = err (71, 1) ("Encoding missing for " ++ show expr)
-- I chose not to encode range explicitly, because the only case where we get it is as an argument of ECall so I treat it there.

-- Method to get the type of an expression
getTypeExpr :: Expr -> Type
getTypeExpr (EConstBool _) = Bool
getTypeExpr (EConstInt _) = Int
getTypeExpr (EBinaryOp lexpr op rexpr) = getTypeExpr lexpr
getTypeExpr (EUnaryOp op expr) = getTypeExpr expr -- This should be boolean, but we can imagine an extension where we add "++" to the language.

getTypeCell :: Cell -> Type
getTypeCell CEmpty = err (82, 20) "Error: refers to empty cell"
getTypeCell (CConst int) = Int
getTypeCell (CInput t mexpr) = t
getTypeCell (CProgram t code post trans) = t


-- This is an augmented data type to the Spreadsheet, so that we can have all the postconditions in a nice format.
type Assumptions = [[(Cell, VExpr)]]

-- Recurse into expr to replace all occ of "value" with "A1" for example
valueToCP :: String -> VExpr -> VExpr
valueToCP var (VVar varName) = if varName == "value" then VVar var else VVar varName -- If we found "value" then do the actual replacing with curr variable name
valueToCP var (VBinaryOp lexpr op rexpr) = VBinaryOp (valueToCP var lexpr) op (valueToCP var rexpr)
valueToCP var (VUnaryOp op expr) = VUnaryOp op (valueToCP var expr)
valueToCP var expr = expr


-- All variables that were already declared in the arguments of a method or in the method itself: so we don't declare anything twice.
type BlackList = [VArgDecl]

inBlacklist :: CellPos -> BlackList -> Bool
inBlacklist cp args = posToString cp `elem` map fst args

--Helper functions to concat both lists of a tuple respectively, and its generalization to list of tuples.
concatTuples :: ([a], [b]) -> ([a], [b]) -> ([a], [b])
concatTuples (a1, b1) (a2, b2) = (a1 ++ a2, b1 ++ b2)

concatList :: [([a], [b])] -> ([a], [b])
concatList = foldl concatTuples ([], [])
--

-- Recurses into an expression and finds all the cells that it uses.
-- Then it declares all of these, assumes their postconds, and adds them to the blacklist.
getAssumesForCells :: Assumptions -> Maybe Expr -> BlackList -> ([VStmt], BlackList)
getAssumesForCells assump (Just (EBinaryOp lexpr op rexpr)) bl =
  concatTuples
    (getAssumesForCells assump (Just lexpr) bl)
    (getAssumesForCells assump (Just rexpr) bl)
getAssumesForCells assump (Just (ECall func_name args)) bl =
  if func_name == "sum" || func_name == "product" || func_name == "operate"
    then
      let (ERange start_cp end_cp) = head args
       in let range = makeRange start_cp end_cp
           in if null range
                then
                  ([], bl)
                else
                  concatList
                    ( map
                        ( \cp ->
                            getAssumesForCells assump (Just (ECell cp)) bl
                        )
                        range
                    )
    else
      undefined -- It's a function name we haven't defined yet.
getAssumesForCells assump (Just (ECell cp)) bl  =
  if inBlacklist cp bl
    then ([], bl) --
    else
      let (cell, assumption) = ( (assump !! snd cp) !! fst cp)
          cellName = posToString cp in
          let typeVar = encodeType (getTypeCell cell)   in
            ( VVarDecl cellName typeVar --finds type
                : [ VAssume (valueToCP cellName assumption)
                  ],
              bl ++ [(cellName, typeVar)] -- The actual adding to the blacklist.
            )
getAssumesForCells assump (Just (EUnaryOp op expr)) bl = getAssumesForCells assump (Just expr) bl -- As I implemented an extension for boolean typed cells.
getAssumesForCells assump arg bl = ([], bl)

-- Encodes each statement. For the return one, it check if we've already encoded one before, if not then it assigns the return value to "value".
encodestmt :: Bool -> Stmt -> VStmt
encodestmt h Skip = VSeq []
encodestmt h (Assign varname expr) = VVarAssign varname (encodeexpr expr)
encodestmt h (Cond expr codeif codeelse) = VIf (encodeexpr expr) (VSeq (map (encodestmt h) codeif)) (VSeq (map (encodestmt h) codeelse))
encodestmt h (Assert expr) = VAssert (encodeexpr expr)
encodestmt h (Local varname vartype mexpr) = VSeq [VVarDecl varname (encodeType vartype), VVarAssign varname (maybe (getDefaultVal vartype) encodeexpr mexpr)]
encodestmt h (Return expr) = if h then encodestmt h Skip else VVarAssign "value" (encodeexpr expr)


-- Calls getAssumesForCells and concats the results.
encodestmtassump :: Assumptions -> Bool -> BlackList -> Stmt -> ([VStmt], BlackList)
encodestmtassump assump h bl (Local varname vartype mexpr) = getAssumesForCells assump mexpr bl
encodestmtassump assump h bl (Assign varname expr) = getAssumesForCells assump (Just expr) bl
encodestmtassump assump h bl (Cond expr codeif codeelse) =
  concatTuples
    ( concatTuples
        ( getAssumesForCells assump (Just expr) bl
        )
        (concatList (map (encodestmtassump assump h bl) codeif))
    )
    (concatList (map (encodestmtassump assump h bl) codeelse))
encodestmtassump assump h bl (Return expr) = getAssumesForCells assump (Just expr) bl
encodestmtassump assump h bl (Assert expr) = getAssumesForCells assump (Just expr) bl
encodestmtassump assump h bl stmt = ([], bl)

-- This is just because we always need to first declare the vars we are going to use, and then encode the statements as normal.
encodestmtassumphelper :: Assumptions -> Bool -> Stmt -> BlackList -> (VStmt, BlackList)
encodestmtassumphelper assump h stmt bl =
  let res = encodestmtassump assump h bl stmt
   in (VSeq (fst res ++ [encodestmt h stmt]), snd res)

encodestmts :: Bool -> Code -> [VStmt]
encodestmts h [] = []
encodestmts h (x : xs) =
  case x of
    Return _ -> encodestmt h x : encodestmts True xs
    _ -> encodestmt h x : encodestmts h xs

encodestmtsassump :: Assumptions -> Bool -> Code -> BlackList -> [VStmt]
encodestmtsassump assump h (x : xs) bl =
  let res = encodestmtassumphelper assump h x bl
   in case x of
        Return _ -> fst res : encodestmtsassump assump True xs (snd res)
        _ -> fst res : encodestmtsassump assump h xs (snd res)
encodestmtsassump assump h [] bl = []

encodeType :: Type -> VType
encodeType Int = VSimpleType "Int"
encodeType Bool = VSimpleType "Bool"

getDefaultVal :: Type -> VExpr
getDefaultVal Int = VIntLit 0
getDefaultVal Bool = VFalseLit

getReturnDecl :: Code -> Type -> [VArgDecl]
getReturnDecl [] t = []
getReturnDecl (x : xs) t =
  case x of
    Return expr -> [("value", encodeType t)] -- TODO re-use getTypeExpr??
    Cond expr ifcode elsecode -> getReturnDecl ifcode t ++ getReturnDecl elsecode t ++ getReturnDecl xs t
    _ -> getReturnDecl xs t

getPost :: Code -> VExpr
getPost [] = VTrueLit
getPost (x : xs) =
  case x of
    Return expr -> VBinaryOp (encodeexpr (EVar "value")) "==" (encodeexpr expr)
    _ -> getPost xs

-- Default method to encode a cell. We make the design choice of representing anything that's not a program by a comment.
-- We also keep all the postconds of each cell, so that when we need to implement an extension, we have all the required information
-- at hand inside the Haskell part; we can implement the necessary checks before converting the spreadsheet to Viper.
encodeprogram :: Cell -> VMember
encodeprogram CEmpty = VMemberComment ""
encodeprogram (CConst int) = VMemberComment ("Const Value = " ++ show int)
encodeprogram (CInput t mexpr) = VMemberComment ("Input of type " ++ show t ++ maybe "" (\expr -> " : requires " ++ show (encodeexpr expr)) mexpr)
encodeprogram (CProgram t code post trans) =
  VMethod
    "run"
    []
    (getReturnDecl code t)
    []
    [ if trans
        then getPost code
        else maybe VTrueLit encodeexpr post
    ]
    (Just (VSeq (encodestmts False code)))


isEmptyCommentOrProgram :: Cell -> Bool
isEmptyCommentOrProgram CEmpty = True
isEmptyCommentOrProgram (CProgram {}) = True
isEmptyCommentOrProgram _ = False

getBlacklist :: Assumptions -> Type -> Expr -> [VArgDecl] -- returns all the cells referred to in the postcond
getBlacklist a t (EParens e) = getBlacklist a t e
getBlacklist a t (EUnaryOp op e) = getBlacklist a t e
getBlacklist a t (EBinaryOp e1 op e2) = getBlacklist a t e1 ++ getBlacklist a t e2
getBlacklist a t (ECell cellPos) =
  -- check that is not cell empty/comment/program
  if isEmptyCommentOrProgram (fst ((a !! snd cellPos) !! fst cellPos))
    then err (255, 50) "Tried to use value of empty, comment or program cells in postcondition"
    else [(posToString cellPos, encodeType t)]
getBlacklist a t arg = []

-- Turns a blacklist into a list of preconditions by finding the postconditions of every cell.
getPrecond :: Assumptions -> [VArgDecl] -> [VExpr]
getPrecond a ((n, t) : xs) =
  let cp = stringToPos n
   in valueToCP n (snd ((a !! snd cp) !! fst cp)) : getPrecond a xs
getPrecond _ [] = []

-- Encodes a program using the assumptions collected before as well as the cell position to call the cell appropriately.
-- We only change how we encode programs, we leave all the rest the same.
encodeprogramcpassump :: Assumptions -> (CellPos, Cell) -> VMember
encodeprogramcpassump assump (cp, CProgram t code post trans) =
  let blackList = maybe [] (getBlacklist assump t) post
   in VMethod
        ("m" ++ posToString cp)
        (if trans then [] else blackList)
        (let ret = getReturnDecl code t in ([head ret | not (null ret)]))
        (getPrecond assump blackList)
        [ if trans
            then getPost code
            else maybe VTrueLit encodeexpr post
        ]
        (Just (VSeq (encodestmtsassump assump False code blackList)))
encodeprogramcpassump assump (cp, cell) = encodeprogram cell

-- Convert every cell into a cell and its postcondition: what it guarantees on the value produced by it. Also we format it nicely so that
-- the parts of the code that need these can use them as is.
cellToAssumption :: (CellPos, Cell) -> (Cell, VExpr)
cellToAssumption (cp, CEmpty) = (CEmpty, VNullLit)
cellToAssumption (cp, CConst int) = (CConst int, VBinaryOp (VVar (posToString cp)) "==" (VIntLit (toInteger int)))
cellToAssumption (cp, CInput t mexpr) = (CInput t mexpr, maybe VTrueLit encodeexpr mexpr)
cellToAssumption (cp, CInputBool mexpr) = (CInputBool mexpr, maybe VTrueLit encodeexpr mexpr)
cellToAssumption (cp, CProgram t code post trans) =
  ( CProgram t code post trans,
    if trans
      then getPost code
      else maybe VTrueLit encodeexpr post
  )


fillViperExpr :: [[(CellPos, Cell)]] -> Assumptions
fillViperExpr = map (map cellToAssumption)

-- CYCLE CHECKING PART BEGIN --
type Dependencies = [CellPos]

type SpreadsheetDependencies = [[Dependencies]]

getECells :: Expr -> Dependencies
getECells (EParens e) = getECells e
getECells (EUnaryOp op e) = getECells e
getECells (EBinaryOp e1 op e2) = getECells e1 ++ getECells e2
getECells (ECell cellPos) = [cellPos]
getECells _ = []

--Function to get dependencies of a statement, so all the cells that it depends on.
getStmtDependencies :: Stmt -> Dependencies
getStmtDependencies Skip = []
getStmtDependencies (Assign varname expr) = getECells expr
getStmtDependencies (Cond expr codeif codeelse) = getECells expr ++ concatMap getStmtDependencies codeif ++ concatMap getStmtDependencies codeelse
getStmtDependencies (Assert expr) = getECells expr
getStmtDependencies (Local varname vartype mexpr) = maybe [] getECells mexpr
getStmtDependencies (Return expr) = getECells expr

getCellDependency :: Cell -> Dependencies
getCellDependency (CProgram t code post trans) = concatMap getStmtDependencies code
getCellDependency _ = []

getSpreadsheetDependencies :: Spreadsheet -> SpreadsheetDependencies
getSpreadsheetDependencies = map (map getCellDependency)


-- Checks if any cell in the dependency list has current cell in its own dependency list.
check :: SpreadsheetDependencies -> (CellPos, Dependencies) -> Bool
check sheetDep (cp, depList) = any (\el -> cp `elem` ((sheetDep !! snd el) !! fst el)) depList

-- Applies check function to each cell
checkIfCycleSpreadsheet :: [(CellPos, Dependencies)] -> SpreadsheetDependencies -> Bool
checkIfCycleSpreadsheet arg sheet = any (check sheet) arg
-- CYCLE CHECKING PART END --


-- A function to traverse a 2D list with indices (col, row)
traverseWithIndices :: [[a]] -> [[((Int, Int), a)]]
traverseWithIndices xs =
  [ [ ((j, i), x)
      | (j, x) <- zip [0 ..] row
    ]
    | (i, row) <- zip [0 ..] xs
  ]

-- A function to make a 2D list into a 1D list we can traverse with indices (col, row)
traverseWithIndices1D :: [[a]] -> [((Int, Int), a)]
traverseWithIndices1D xs =
  [ ((j, i), x)
    | (i, row) <- zip [0 ..] xs,
      (j, x) <- zip [0 ..] row
  ]

encode :: Spreadsheet -> VProgram
encode sheet =
  let newSheet = mapIteratedCells sheet
   in let sheetDep = getSpreadsheetDependencies newSheet
       in if checkIfCycleSpreadsheet (traverseWithIndices1D sheetDep) sheetDep
            then
              err (363, 10) ("Cycle detected, not proceeding with encoding" ++ show sheetDep)
            else
              let sheet_with_indices = traverseWithIndices newSheet
               in let assump = fillViperExpr sheet_with_indices
                   in VProgram
                        ( concatMap
                            ( map
                                ( encodeprogramcpassump assump
                                )
                            )
                            sheet_with_indices
                        )
                        ""

-- Turns iterated cells into input cells with preconditions matching the actual value each cell should hold.
mapIteratedCell :: Cell -> [Cell]
mapIteratedCell (CIterated [EConstInt len, init_val, op]) =
  let newls = take len (iterate (`replaceXInArg` op) init_val)
   in map (CInput Int . Just . EBinaryOp (EVar "value") "==") newls
mapIteratedCell cell = [cell]

mapIteratedCells :: Spreadsheet -> Spreadsheet
mapIteratedCells = map (concatMap mapIteratedCell)