--------------------------
-- VIPER PRETTY PRINTER --
--------------------------

-- This module provides a pretty-printer for Viper programs. It is used by the
-- entrypoint in `Main.hs` when using the `encode` command.

module Viper.Printer (
  renderVExpr,
  renderVMember,
  renderVProgram,
) where

import Data.List

import Viper.Ast

(<+>) :: String -> String -> String
r <+> s = r ++ " " ++ s

renderVType :: VType -> String
renderVType tp = case tp of
  VSimpleType t -> t
  VGenericType t args -> t ++ "[" ++ (intercalate ", " (map renderVType args)) ++ "]"

renderVExpr :: VExpr -> String
renderVExpr sds = case sds of
  VIntLit i -> (show i)
  VTrueLit -> "true"
  VFalseLit -> "false"
  VNullLit -> "null"
  VVar n -> n
  VSeqLit contents -> "Seq" ++ renderParens (renderCommaSep contents)
  VSetLit contents -> "Set" ++ renderParens (renderCommaSep contents)
  VMultisetLit contents -> "Multiset" ++ renderParens (renderCommaSep contents)
  VMapLit contents -> "Map" ++ renderParens (renderMapContents contents)
  VBinaryOp e1 op e2 -> renderParens $ (renderVExpr e1) <+> (op) <+> (renderVExpr e2)
  VUnaryOp op e1 -> renderParens $ op ++ (renderVExpr e1)
  VFuncApp name args -> (name) ++ renderParens (renderCommaSep args)
  VSeqIndex e1 e2 -> renderVExpr e1 ++ "[" ++ renderVExpr e2 ++ "]"
  VSeqTake e1 e2 -> renderVExpr e1 ++ "[.." ++ renderVExpr e2 ++ "]"
  VSeqDrop e1 e2 -> renderVExpr e1 ++ "[" ++ renderVExpr e2 ++ "..]"
  VSeqUpdate e1 e2 e3 -> renderVExpr e1 ++ "[" ++ renderVExpr e2 <+> ":=" <+> renderVExpr e3 ++ "]"
  VMapLookup e1 e2 -> renderVExpr e1 ++ "[" ++ renderVExpr e2 ++ "]"
  VLength e -> "|" ++ renderVExpr e ++ "|"
  VFieldAcc e f -> renderVExpr e ++ "." ++ f
  VFieldAccPred e f p -> "acc" ++ renderParens (renderVExpr e ++ "." ++ f ++ "," <+> renderVExpr p)
  VPredAccPred prd args p -> "acc" ++ renderParens (prd ++ renderParens (renderCommaSep args) ++ "," <+> renderVExpr p)
  VUnfolding prd args p bod -> renderParens ("unfolding" <+> (renderVExpr (VPredAccPred prd args p)) <+> "in" <+> renderVExpr bod)
  VOld e -> "old" ++ renderParens (renderVExpr e)
  VLabelledOld lbl e -> "old[" ++ lbl ++ "]" ++ renderParens (renderVExpr e)
  VLet v e bod -> renderParens ("let" <+> v <+> "==" <+> renderParens (renderVExpr e) <+> "in" <+> renderVExpr bod)
  VForall vars triggers bod -> renderParens ("forall" <+> renderArgList vars <+> "::" <+> renderTriggers triggers <+> renderVExpr bod)
  VExists vars triggers bod -> renderParens ("exists" <+> renderArgList vars <+> "::" <+> renderTriggers triggers <+> renderVExpr bod)
  VResult -> "result"
  VAdtConstructorApp name args -> name ++ renderParens (renderCommaSep args)
  VAdtDiscriminatorApp e name -> renderVExpr e ++ ".is" ++ name
  VAdtDestructorApp e name -> renderVExpr e ++ "." ++ name
  VRawExpr str -> str
  --VParens expr -> renderParens (renderVExpr expr)

renderTriggers [] = ""
renderTriggers (t : ts) = renderTrigger t <+> renderTriggers ts

renderTrigger exps = "{" <+> renderCommaSep exps <+> "}"

renderParens :: String -> String
renderParens t = "(" ++ t ++ ")"

renderArgList :: [VArgDecl] -> String
renderArgList [] = ""
renderArgList ((var, typ): []) = var ++ ":" <+> renderVType typ
renderArgList ((var, typ): vs) = var ++ ":" <+> renderVType typ ++ "," <+> renderArgList vs

renderCommaSep :: [VExpr] -> String
renderCommaSep [] = ""
renderCommaSep (e: []) = renderVExpr e
renderCommaSep (e: es) = renderVExpr e ++ "," <+> renderCommaSep es

renderMapContents :: [(VExpr, VExpr)] -> String
renderMapContents [] = ""
renderMapContents ((k, v): []) = renderVExpr k <+> ":=" <+> renderVExpr v 
renderMapContents ((k, v): kvs) = renderVExpr k <+> ":=" <+> renderVExpr v ++ "," <+> renderMapContents kvs

renderVStmt :: VStmt -> String
renderVStmt s = case s of
  VVarDecl v t -> "var" <+> v ++ ":" <+> renderVType t
  VVarAssign v e -> v <+> ":=" <+> renderVExpr e
  VFieldAssign e1 f e2 -> renderVExpr e1 ++ "." ++ f <+> ":=" <+> renderVExpr e2
  VNew v fields -> v <+> ":=" <+> "new" ++ renderParens (intercalate ", " fields)
  VMethodCall [] name args -> name ++ renderParens (renderCommaSep args)
  VMethodCall trgts name args -> (intercalate ", " trgts <+> ":=" <+> name ++ renderParens (renderCommaSep args))
  VExhale e -> "exhale" <+> renderVExpr e
  VInhale e -> "inhale" <+> renderVExpr e
  VAssert e -> "assert" <+> renderVExpr e
  VAssume e -> "assume" <+> renderVExpr e
  VFold name args p -> "fold" <+> "acc" ++ renderParens (name ++ renderParens (renderCommaSep args) ++ "," <+> renderVExpr p)
  VUnfold name args p -> "unfold" <+> "acc" ++ renderParens (name ++ renderParens (renderCommaSep args) ++ "," <+> renderVExpr p)
  VLabel name -> "label" <+> name
  VGoto name -> "goto" <+> name
  VSeq stmts -> (intercalate "\n" (map renderVStmt stmts))
  VIf e thn els -> "if" <+> renderParens (renderVExpr e) <+> "{\n" ++ thnText ++ "\n} else {\n" ++ elsText ++ "\n}"
    where thnLines = lines (renderVStmt thn)
          thnText = indent thnLines
          elsLines = lines (renderVStmt els)
          elsText = indent elsLines
  VWhile e invs bod -> "while" <+> renderParens (renderVExpr e) <+> "\n" ++ invText ++ "\n{" ++ bodText ++"\n}"
    where invLines = map (\inv -> "invariant" <+> renderVExpr inv) invs
          invText = indent invLines
          bodLines = lines (renderVStmt bod)
          bodText = indent bodLines
  VComment s -> "//" <+> (concat (lines s))
  VMacroCall name args -> name ++ renderParens (renderCommaSep args)

indent :: [String] -> String
indent [] = ""
indent lines = "  " ++ (intercalate "\n  " lines)

renderVMember :: VMember -> String
renderVMember m = case m of
  VField name typ -> "field" <+> name ++ ":" <+> renderVType typ
  VMethod name args rets pres posts bod -> "method" <+> name ++ renderParens (renderArgList args) <+> "returns" <+> renderParens (renderArgList rets) ++ presText ++ postsText ++ bodText
    where presText = concat $ map (\pre -> "\n  requires" <+> renderVExpr pre) pres
          postsText = concat $ map (\post -> "\n  ensures" <+> renderVExpr post) posts
          bodText = case bod of
            Nothing -> ""
            Just b -> "\n{\n" ++ indent (lines (renderVStmt b)) ++ "\n}"
  VFunction name args typ pres posts bod -> "function" <+> name ++ renderParens (renderArgList args) ++ ":" <+> renderVType typ ++ presText ++ postsText ++ bodText
    where presText = concat $ map (\pre -> "\n  requires" <+> renderVExpr pre) pres
          postsText = concat $ map (\post -> "\n  ensures" <+> renderVExpr post) posts
          bodText = case bod of
            Nothing -> ""
            Just e -> "\n{\n" ++ indent (lines (renderVExpr e)) ++ "\n}"
  VPredicate name args bod -> "predicate" <+> name ++ renderParens (renderArgList args) <+> bodText
    where bodText = case bod of
            Nothing -> ""
            Just e -> "{\n" ++ indent (lines (renderVExpr e)) ++ "\n}"
  VDomain name funcs axioms -> "domain" <+> name <+> "{\n" ++ funcText ++ "\n" ++ axiomsText ++ "\n}"
    where funcLines = map renderVDomainFunction funcs
          funcText = indent funcLines
          axiomParts = map renderVDomainAxiom axioms
          axiomLines = concat $ map lines axiomParts
          axiomsText = indent axiomLines
  VAdtDecl name constrs -> "adt" <+> name <+> "{\n" ++ constrsText ++ "\n}"
    where constrLines = map renderVAdtConstr constrs
          constrsText = indent constrLines
  VMemberComment str -> "// " ++ str
  VMacroExpr name args bod -> "define" <+> name ++ renderParens (intercalate ", " args) <+> "(\n" ++ (renderVExpr bod) ++ "\n)"
  VMacroStmt name args bod -> "define" <+> name ++ renderParens (intercalate ", " args) <+> "{\n" ++ (indent (lines (renderVStmt bod))) ++ "\n}"

renderVAdtConstr :: VAdtConstructorDecl -> String
renderVAdtConstr c = case c of
  VAdtConstructorDecl name args -> name ++ renderParens (renderArgList args)

renderVDomainFunction :: VDomainFunction -> String
renderVDomainFunction f = case f of
  VDomainFunction name args typ -> "function" <+> name ++ renderParens (renderArgList args) ++ ":" <+> renderVType typ

renderVDomainAxiom :: VDomainAxiom -> String
renderVDomainAxiom ax = case ax of
  VDomainAxiom name bod -> "axiom" <+> name <+> "{\n" ++ indent ([renderVExpr bod]) ++ "\n}\n"

renderVProgram :: VProgram -> String
renderVProgram p = case p of
  VProgram members prelude -> memberText ++ "\n" ++ prelude
    where memberParts = map (\m -> renderVMember m ++ "\n") members
          memberText = intercalate "\n" memberParts

-- example: putStr (renderVProgram p), where p is the program.
