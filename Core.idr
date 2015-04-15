module Core

import Data.Fin

%default total

--------------
-- Newtypes --
--------------

Name : Type
Name = String

Code : Type
Code = String

----------------------
-- Core Expressions --
----------------------

--mutual
data CLiteral : Type where
    CLitCode  : Code  -> CLiteral

    CLitFlt   : Float -> CLiteral
    CLitInt   : Int   -> CLiteral
    CLitUInt  : Nat   -> CLiteral
    CLitBool  : Bool  -> CLiteral

    CBinOp    : Name -> CLiteral
    CPreUnOp  : Name -> CLiteral
    CPostUnOp : Name -> CLiteral

    CPair     : CLiteral

{-
      CBinOp    : Name  → CExpr → CExpr → CLiteral
      CPreUnOp  : Name  → CExpr →         CLiteral
      CPostUnOp : Name  → CExpr →         CLiteral

      CPair     : CExpr → CExpr → CLiteral
-}

data CExpr : Type where
    CVar : Name                -> CExpr
    CLit : CLiteral            -> CExpr
    CApp : CExpr -> List CExpr -> CExpr

CApp' : CExpr -> CExpr -> CExpr
CApp' (CApp f xs) x = CApp f (xs ++ [x])
CApp' f x = CApp f [x]

-----------------------------
-- Core Types / Qualifiers --
-----------------------------

data CScalar : Type where
    CFloat  : CScalar
    CDouble : CScalar
    CInt    : CScalar
    CUInt   : CScalar
    CBool   : CScalar
    CVoid   : CScalar

data CType : Type where
    CScalarTy    : CScalar -> CType
    CVec         : CScalar -> Fin 5 -> CType
    CMat         : CScalar -> Fin 5 -> Fin 5 -> CType
    CArray       : CType -> {- CExpr -} Nat -> CType
    CSampler     : Fin 4 -> CType
    CSamplerCube : CType

    CProduct     : CType -> CType -> CType

LayoutQual : Type
LayoutQual = (String, Maybe Int)

LayoutQualifier : Type
LayoutQualifier = List LayoutQual

data StorageQualifier : Type where
    Const       : StorageQualifier

    In          : StorageQualifier
    Out         : StorageQualifier
    Uniform     : StorageQualifier
    Buffer      : StorageQualifier

    CentroidIn  : StorageQualifier
    CentroidOut : StorageQualifier
    SampleIn    : StorageQualifier
    SampleOut   : StorageQualifier
    PatchIn     : StorageQualifier
    PatchOut    : StorageQualifier

data InterpolationQualifier : Type where
    Flat             : InterpolationQualifier
    NoPerspective    : InterpolationQualifier
    Smooth           : InterpolationQualifier

data Qualifier : Type where
    MkQualifier :
        Maybe LayoutQualifier ->
        Maybe StorageQualifier ->
        Maybe InterpolationQualifier ->
        Qualifier

storageQ : StorageQualifier -> Qualifier
storageQ q = MkQualifier Nothing (Just q) Nothing

inQ : Qualifier
inQ = storageQ In

uniformQ : Qualifier
uniformQ = storageQ Uniform

outQ : Qualifier
outQ = storageQ Out

noQ : Qualifier
noQ = MkQualifier Nothing Nothing Nothing

FullType : Type
FullType = (CType, Qualifier)

FullVar : Type
FullVar = (FullType, Name)

---------------------
-- Core Statements --
---------------------

data CDefinition : Type where
    CDefine : CType -> Name -> CExpr -> CDefinition

mutual
    data CaseExpr : Type where
        Case    : CExpr -> CStatement -> CaseExpr
        Default : CStatement -> CaseExpr

    data CStatement : Type where
        DoExpr       : CExpr -> CStatement
        SequenceStmt : CStatement -> CStatement -> CStatement

        DefineStmt : CDefinition -> CStatement
        Assign     : Name -> CExpr -> CStatement

        If     : CExpr -> CStatement -> Maybe CStatement -> CStatement
        Switch : CExpr -> List CaseExpr -> CStatement

        While   : CExpr -> CStatement -> CStatement
        DoWhile : CExpr -> CStatement -> CStatement

        For : CDefinition -> CExpr -> CStatement -> CStatement -> CStatement

        Continue : CStatement
        Break    : CStatement
        Return   : Maybe CExpr -> CStatement
        Discard  : CStatement

data Profile : Type where
    Core          : Profile
    Compatibility : Profile
    Es            : Profile

data CTopLevel : Type where
    DeclVar : FullVar -> CTopLevel
    DeclFun : CType -> Name -> List FullVar -> CStatement -> CTopLevel

    Version     : Nat -> Maybe Profile -> CTopLevel
    RawTopLevel : String -> CTopLevel
