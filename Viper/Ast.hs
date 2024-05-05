--------------------------
-- VIPER AST DEFINITION --
--------------------------

-- Here we define the abstract syntax tree (AST) for Viper programs. Instances
-- of such ASTs should be created by your `encode` function, implemented in
-- `Encoder/Encoder.hs`.

module Viper.Ast where

-- Viper AST

type VFieldName = String
type VVarName = String
type VPredName = String

type VArgDecl = (VVarName, VType)

data VType = VSimpleType String
  | VGenericType String [VType]
    deriving (Eq, Show)

data VExpr =
    VIntLit Integer
  | VTrueLit
  | VFalseLit
  | VNullLit
  | VVar VVarName
  | VSeqLit [VExpr]
  | VSetLit [VExpr]
  | VMultisetLit [VExpr]
  | VMapLit [(VExpr, VExpr)]  -- list of key-value-pairs
  | VBinaryOp VExpr String VExpr  -- all binary operations, including ==>, ++, union, setminus, ...
  | VUnaryOp String VExpr
  | VSeqIndex VExpr VExpr
  | VSeqTake VExpr VExpr  -- s[..i]
  | VSeqDrop VExpr VExpr  -- s[i..]
  | VSeqUpdate VExpr VExpr VExpr  -- s[i := e]
  | VMapLookup VExpr VExpr  -- m[k := v]
  | VLength VExpr -- length for sequences, cardinality for sets/maps
  | VFuncApp String [VExpr]  -- fun(args)
  | VFieldAcc VExpr VFieldName  -- e.f
  | VFieldAccPred VExpr VFieldName VExpr  -- acc(e.f, p)
  | VPredAccPred VPredName [VExpr] VExpr  -- acc(P(args), p)
  | VUnfolding VPredName [VExpr] VExpr VExpr  -- unfolding acc(P(args), p) in e
  | VOld VExpr  -- old(e)
  | VLabelledOld String VExpr  -- old[label](e)
  | VLet VVarName VExpr VExpr  -- let x == (e) in e'
  | VForall [VArgDecl] [[VExpr]] VExpr  -- forall args :: {e1, e2} {e3} e
  | VExists [VArgDecl] [[VExpr]] VExpr  -- exists args :: {e1, e2} {e3, e4} e
  | VResult  -- result (for function postconditions only)
  | VAdtConstructorApp String [VExpr]  -- Cons(args)
  | VAdtDiscriminatorApp VExpr String  -- e.isCons
  | VAdtDestructorApp VExpr String  -- e.tail
  | VRawExpr String
    deriving (Eq, Show)

data VStmt =
    VVarDecl VVarName VType
  | VVarAssign VVarName VExpr
  | VFieldAssign VExpr VFieldName VExpr
  | VNew VVarName [VFieldName]
  | VMethodCall [VVarName] String [VExpr]
  | VExhale VExpr
  | VInhale VExpr
  | VAssert VExpr
  | VAssume VExpr
  | VFold VPredName [VExpr] VExpr  -- fold acc(P(args), p)
  | VUnfold VPredName [VExpr] VExpr  -- unfold acc(P(args), p)
  | VSeq [VStmt]
  | VIf VExpr VStmt VStmt
  | VWhile VExpr [VExpr] VStmt
  | VLabel String
  | VGoto String
  | VComment String -- for optional documentation of the generated Viper program
  | VMacroCall String [VExpr] -- call to a macro as a statement, to avoid generating `:=`
    deriving (Eq, Show)

data VMember =
    VField VFieldName VType
  | VMethod String [VArgDecl] [VArgDecl] [VExpr] [VExpr] (Maybe VStmt)
  | VFunction String [VArgDecl] VType [VExpr] [VExpr] (Maybe VExpr)
  | VPredicate String [VArgDecl] (Maybe VExpr)
  | VDomain String [VDomainFunction] [VDomainAxiom]
  | VAdtDecl String [VAdtConstructorDecl]
  | VMemberComment String -- top-level comments, for readability of generated file
  | VMacroExpr String [VVarName] VExpr -- declaration of an expression-like macro
  | VMacroStmt String [VVarName] VStmt -- declaration of a statement-like macro
    deriving (Eq, Show)

data VAdtConstructorDecl = VAdtConstructorDecl String [VArgDecl]
                           deriving (Eq, Show)

data VDomainAxiom = VDomainAxiom String VExpr
                    deriving (Eq, Show)

data VDomainFunction = VDomainFunction String [VArgDecl] VType
                       deriving (Eq, Show)

data VProgram = VProgram [VMember] String
  -- programs include an arbitrary string for additional definitions.
                deriving (Eq, Show)
