module FrontToCore

import Data.Fin

import Front
import Core

import CoreToString

%default total

scalarToCore : {A : Type} -> Scalar A -> CScalar
scalarToCore void  = CVoid
scalarToCore bool  = CBool
scalarToCore int   = CInt
scalarToCore uint  = CUInt
scalarToCore float = CFloat

typeToCore : {A : Type} -> Ty A -> CType
typeToCore (scalar scTy) = CScalarTy (scalarToCore scTy)
typeToCore (sampler n) = CSampler n
typeToCore samplerCube = CSamplerCube
typeToCore (vec scTy n) =
    CVec (scalarToCore scTy) n
typeToCore (mat scTy n m) =
    CMat (scalarToCore scTy) n m
typeToCore (array ty n) =
    CArray (typeToCore ty) n
typeToCore ((&) a b)  = CProduct (typeToCore a) (typeToCore b)
typeToCore ((~>) a b) = typeToCore b
typeToCore Any      = CScalarTy CVoid -- Doesn't matter

declVars : {A : Type} -> Expr A -> List CTopLevel
declVars (Lam (MkV ty var) body) =
    DeclVar ((typeToCore ty, MkQualifier Nothing (Just In) Nothing), var) ::
    declVars body
declVars (f :$ x) = declVars x
declVars _ = []

toBody : {A : Type} -> Expr A -> Sigma Type (\B => Expr B) --(b : Type ** Expr b)
toBody (Lam _ body) = toBody body
toBody {A} body     = (A ** body)

declFun : {A : Type} -> Name -> Expr A -> List CTopLevel
declFun nameStr expr = assert_total $
    let (params, (_ ** body)) = collectParams expr
        (tops, expr) = assert_total (genBody body)
        decl = DeclFun (CScalarTy CVoid)
                       nameStr
                       params
                       (Return (Just expr))
    in tops ++ [decl]
  where
    litToCore : {A : Type} -> Lit A -> CLiteral
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

    collectParams : {A : Type} ->
        Expr A -> (List FullVar, Sigma Type (\B => Expr B))
    collectParams (Lam (MkV ty name) body) =
        let (rest, endBody) = collectParams body
            wholeList = ((typeToCore ty, noQualifier), name) :: rest
        in (wholeList, endBody)
    collectParams {A} body = ([], (A ** body))

    partial genBody : {A : Type} -> Expr A -> (List CTopLevel, CExpr)
    genBody (Var name)  = ([], CVar name)
    genBody (Literal x) = ([], CLit (litToCore x))
    genBody (LamLit _)  = ([], CVar "error: see FrontToCore.idr:101")
    genBody (Lam var body) =
        let name' = nameStr ++ "_prime"
            fun = declFun name' (Lam var body)
        in (fun, CVar name')
    genBody (f :$ x) =
        let (tf, f') = genBody f
            (tx, x') = genBody x
        in (tf ++ tx, CApp' f' x')

declMain : {A : Type} -> Expr A -> List CTopLevel
declMain expr =
    let varDecls = declVars expr
        (_ ** body) = toBody expr
    in varDecls ++ declFun "main" body





infixr 5 *#
(*#) : {A, B, C : Type} -> Expr A -> Expr B -> Expr C
a *# b = Literal (BinOp "*") :$ a :$ b

vec4 : Expr (Vect 3 Float) -> Expr Float -> Expr (Vect 4 Float)
vec4 xyz w = Literal (LitCode "vec4") :$ xyz :$ w

{-
glPosition : Expr (Vec Float 3 -> Vec Float 3 -> Mat Float 4 4 -> Vec Float 4)
glPosition =
    LamLit $ \vertPos_modelSpace =>
    LamLit $ \vertexColor =>
    LamLit $ \mvp =>
        mvp
    Λ MkV (float vec⟦ 3 ⟧) "vertPos_modelSpace" ⇝
    Λ MkV (float vec⟦ 3 ⟧) "vertexColor" ⇝
    Λ MkV (float mat⟦ 4 ⟧⟦ 4 ⟧) "mvp" ⇝
    (Var "mvp" *# vec4 (Var "vertPos_modelSpace")
                      (Literal (LitFlt 1.0)))
-}
{-
glPosStr : String
glPosStr = concatStr (L.map showTopLevel (declMain glPosition))
-}
