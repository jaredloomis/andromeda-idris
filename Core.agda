module Core where

open import Data.String
open import Data.Float
open import Data.Char
open import Data.Nat
open import Data.Integer
open import Data.Bool

open import Data.Maybe

open import Data.List as L
open import Data.Vec

open import Data.Product

--------------
-- Newtypes --
--------------

Name : Set
Name = String

Code : Set
Code = String

----------------------
-- Core Expressions --
----------------------

--mutual
data CLiteral : Set where
    CLitCode  : Code  → CLiteral

    CLitFlt   : Float → CLiteral
    CLitInt   : ℤ     → CLiteral
    CLitUInt  : ℕ     → CLiteral
    CLitBool  : Bool  → CLiteral

    CBinOp    : Name → CLiteral
    CPreUnOp  : Name → CLiteral
    CPostUnOp : Name → CLiteral

    CPair     : CLiteral

{-
      CBinOp    : Name  → CExpr → CExpr → CLiteral
      CPreUnOp  : Name  → CExpr →         CLiteral
      CPostUnOp : Name  → CExpr →         CLiteral

      CPair     : CExpr → CExpr → CLiteral
-}

data CExpr : Set where
    CVar : Name               → CExpr
    CLit : CLiteral           → CExpr
    CApp : CExpr → List CExpr → CExpr

CApp' : CExpr → CExpr → CExpr
CApp' (CApp f xs) x = CApp f (xs L.++ (x ∷ []))
CApp' f x = CApp f (x ∷ [])

-----------------------------
-- Core Types / Qualifiers --
-----------------------------

data CScalar : Set where
    CFloat  : CScalar
    CDouble : CScalar
    CInt    : CScalar
    CUInt   : CScalar
    CBool   : CScalar
    CVoid   : CScalar

data CType : Set where
    CScalarTy    : CScalar → CType
    _CVec⟦_⟧     : CScalar → ℕ → CType
    _CMat⟦_⟧⟦_⟧  : CScalar → ℕ → ℕ → CType
    _CArray⟦_⟧   : CType → {- CExpr -} ℕ → CType
    CSampler     : ℕ → CType
    CSamplerCube : CType

    CProduct     : CType -> CType -> CType

LayoutQual : Set
LayoutQual = String × Maybe ℕ

LayoutQualifier : Set
LayoutQualifier = List LayoutQual

data StorageQualifier : Set where
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

data InterpolationQualifier : Set where
    Flat             : InterpolationQualifier
    NoPerspective    : InterpolationQualifier
    Smooth           : InterpolationQualifier

data Qualifier : Set where
    MkQualifier :
        Maybe LayoutQualifier →
        Maybe StorageQualifier →
        Maybe InterpolationQualifier →
        Qualifier

noQualifier : Qualifier
noQualifier = MkQualifier nothing nothing nothing

FullType : Set
FullType = CType × Qualifier

FullVar : Set
FullVar = FullType × Name

---------------------
-- Core Statements --
---------------------

data CDefinition : Set where
    CDefine : CType → Name → CExpr → CDefinition

mutual
    data CaseExpr : Set where
        Case    : CExpr → CStatement → CaseExpr
        Default : CStatement → CaseExpr

    data CStatement : Set where
        DoExpr       : CExpr → CStatement
        SequenceStmt : CStatement → CStatement → CStatement

        DefineStmt : CDefinition → CStatement
        Assign     : Name → CExpr → CStatement

        If     : CExpr → CStatement → Maybe CStatement → CStatement
        Switch : CExpr → List CaseExpr → CStatement

        While   : CExpr → CStatement → CStatement
        DoWhile : CExpr → CStatement → CStatement

        For : CDefinition → CExpr → CStatement → CStatement → CStatement

        Continue : CStatement
        Break    : CStatement
        Return   : Maybe CExpr → CStatement
        Discard  : CStatement

data Profile : Set where
    Core          : Profile
    Compatibility : Profile
    Es            : Profile

data CTopLevel : Set where
    DeclVar : FullVar → CTopLevel
    DeclFun : CType → Name → List FullVar → CStatement → CTopLevel

    Version     : ℕ → Maybe Profile → CTopLevel
    RawTopLevel : String → CTopLevel
