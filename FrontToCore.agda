{-# OPTIONS --no-termination-check #-}
module FrontToCore where

open import Data.Nat
open import Data.String as S
open import Data.Maybe
open import Data.List as L
open import Data.Product

open import Front
open import Core

open import CoreToString

scalarToCore : {A : Set} -> Scalar A -> CScalar
scalarToCore void  = CVoid
scalarToCore bool  = CBool
scalarToCore int   = CInt
scalarToCore uint  = CUInt
scalarToCore float = CFloat

typeToCore : {A : Set} → Type A → CType
typeToCore (scalar scTy) = CScalarTy (scalarToCore scTy)
typeToCore (sampler n) = CSampler n
typeToCore samplerCube = CSamplerCube
typeToCore (scTy vec⟦ n ⟧) =
    (scalarToCore scTy) CVec⟦ n ⟧
typeToCore (scTy mat⟦ n ⟧⟦ m ⟧) =
    (scalarToCore scTy) CMat⟦ n ⟧⟦ m ⟧
typeToCore (ty array⟦ n ⟧) =
    (typeToCore ty) CArray⟦ n ⟧
typeToCore (a ×× b) = CProduct (typeToCore a) (typeToCore b)
typeToCore (a ~> b) = typeToCore b

declVars : {A : Set} → Expr A → List CTopLevel
declVars (Λ (MkV ty var) ⇝ body) =
    DeclVar ((typeToCore ty , MkQualifier nothing (just In) nothing) , var) ∷
    declVars body
declVars (f ∙$ x) = declVars x
declVars _ = []

toBody : {A C : Set} → ({B : Set} → Expr B → C) → Expr A → C
toBody f (Λ _ ⇝ body) = toBody f body
toBody f body         = f body

declFun : {A : Set} → Name → Expr A → List CTopLevel
declFun nameStr expr =
    let (params , (_ , body)) = collectParams expr
        (tops , expr) = genBody body
        decl = DeclFun (CScalarTy CVoid)
                       nameStr
                       params
                       (Return (just expr))
    in tops L.++ (decl ∷ [])
  where
    litToCore : {A : Set} → Lit A -> CLiteral
    litToCore (LitFlt   f)       = CLitFlt   f
    litToCore (LitBool  b)       = CLitBool  b
    litToCore (LitInt   i)       = CLitInt   i
    litToCore (LitUInt  u)       = CLitUInt  u
    litToCore (LitCode  c)       = CLitCode  c
    litToCore (PreUnOp  o)       = CPreUnOp  o
    litToCore (PostUnOp o)       = CPostUnOp o
    litToCore (BinOp    o)       = CBinOp   o
--    litToCore (FieldSelection s) = CFieldSelection s
    litToCore Pair               = CPair

    collectParams : {A : Set} → Expr A → List FullVar × (∃ λ a → Expr a)
    collectParams (Λ (MkV ty name) ⇝ body) =
        let (rest , endBody) = collectParams body
            wholeList = ((typeToCore ty , noQualifier) , name) ∷ rest
        in (wholeList , endBody )
    collectParams {A} body = ([] , (A , body))

{-
    collectArgs : {A : Set} → Expr A → List (∃ λ a → Expr a) × (∃ λ a → Expr a)
    collectArgs {A} (f ∙$ x) =
        let (rest , endBody) = collectArgs f
            wholeList = (_ , x) ∷ rest
        in (wholeList , endBody)
    collectArgs {A} body = ([] , (A , body))
-}

    genBody : {A : Set} → Expr A → List CTopLevel × CExpr
    genBody (Var (MkV _ name)) = ([] , CVar name)
    genBody (Literal x)        = ([] , CLit (litToCore x))
    genBody (Λ var ⇝ body) =
        let name' = nameStr S.++ "_prime"
            fun = declFun name' (Λ var ⇝ body)
        in (fun , CVar name')
    genBody (f ∙$ x) =
        let (tf , f') = genBody f
            (tx , x') = genBody x
        in (tf L.++ tx , CApp' f' x')


doubleF : Expr (ℕ → ℕ)
doubleF =
    let n = MkV (scalar uint) "n"
    in Λ n ⇝
        let plus = Literal (BinOp "+")
        in (plus ∙$ Var n) ∙$ Var n

doubleC : List CTopLevel
doubleC = declFun "main_prime" doubleF

doubleStr : String
doubleStr = concatStr (L.map showTopLevel doubleC)
