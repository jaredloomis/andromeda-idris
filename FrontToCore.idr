module FrontToCore

import Data.Fin
import Control.Monad.State
import Control.Monad.Identity

import Front
import Core

import CoreToString

%default total

-- Elaboration types --

record ElabState : Type where
    ES : (nameSeed : Nat) ->
         ElabState

ElabM : Type -> Type
ElabM a = State ElabState a

runElabM : ElabM a -> ElabState -> a
runElabM e = fst . runIdentity . runStateT e

-- Generating unique var names --

freshName : ElabM Name
freshName = do
    n <- gets nameSeed
    modify $ \es => record {nameSeed = nameSeed es + 1} es
    return $ "andromeda_var_name" ++ show n

-- Elaboration --

scalarToCore : Scalar a -> CScalar
scalarToCore void  = CVoid
scalarToCore bool  = CBool
scalarToCore int   = CInt
scalarToCore uint  = CUInt
scalarToCore float = CFloat

typeToCore : Ty a -> CType
typeToCore (scalar scTy) = CScalarTy (scalarToCore scTy)
typeToCore (sampler n) = CSampler n
typeToCore samplerCube = CSamplerCube
typeToCore (vec n scTy) =
    CVec (scalarToCore scTy) n
typeToCore (mat n m scTy) =
    CMat (scalarToCore scTy) n m
typeToCore (array n ty) =
    CArray (typeToCore ty) n
typeToCore ((&) a b)  = CProduct (typeToCore a) (typeToCore b)
typeToCore ((~>) a b) = typeToCore b
typeToCore Any      = CScalarTy CVoid -- Doesn't matter

declVars : Expr a -> ElabM (List CTopLevel, Sigma Type (\b => Expr b))
declVars (LamLit q ty f) = do
    name <- freshName
    let expr = f (MkV ty name)
    (rest, endBody) <- declVars expr
    return (DeclVar
        ((typeToCore ty, q), name) ::
        rest, endBody)
declVars (Lam q (MkV ty var) body) = do
    (rest, endBody) <- declVars body
    return (DeclVar
        ((typeToCore ty, q), var) ::
        rest, endBody)
declVars expr = return ([], (_ ** expr))

declFun : Name -> Expr a -> List CTopLevel
declFun nameStr expr = assert_total $
    let (params, (_ ** body)) = collectParams expr
        (tops, expr) = assert_total (genBody body)
        decl = DeclFun (CScalarTy CVoid)
                       nameStr
                       params
                       (Return (Just expr))
    in tops ++ [decl]
  where
    litToCore : Lit a -> CLiteral
    litToCore (LitFlt   f)       = CLitFlt   f
    litToCore (LitBool  b)       = CLitBool  b
    litToCore (LitInt   i)       = CLitInt   i
    litToCore (LitUInt  u)       = CLitUInt  u
    litToCore (LitCode  c)       = CLitCode  c
    litToCore (PreUnOp  o)       = CPreUnOp  o
    litToCore (PostUnOp o)       = CPostUnOp o
    litToCore (BinOp    o)       = CBinOp   o
    litToCore Pair               = CPair

    collectParams :
        Expr a -> (List FullVar, Sigma Type (\b => Expr b))
    collectParams (LamLit q ty f) =
        let name = "tmp_andromeda_name"
            expr = f (MkV ty name)
            thisParam = ((typeToCore ty, q), name)
            (otherParams, endBody) = collectParams expr
        in (thisParam :: otherParams, endBody)
    collectParams (Lam q (MkV ty name) body) =
        let (rest, endBody) = collectParams body
            wholeList = ((typeToCore ty, q), name) :: rest
        in (wholeList, endBody)
    collectParams {a} body = ([], (a ** body))

    genBody : Expr a -> (List CTopLevel, CExpr)
    genBody (Ref name)  = ([], CVar name)
    genBody (Literal x) = ([], CLit (litToCore x))
    genBody (LamLit _ _ _)  = ([], CVar "error: see FrontToCore.idr")
    genBody (Lam q var body) =
        let name' = nameStr ++ "_prime"
            fun = declFun name' (Lam q var body)
        in (fun, CVar name')
    genBody (f :$ x) =
        let (tf, f') = genBody f
            (tx, x') = genBody x
        in (tf ++ tx, CApp' f' x')

declMain : Expr a -> ElabM (List CTopLevel)
declMain expr = do
    (varDecls, (_ ** body)) <- declVars expr
    return $ varDecls ++ declFun "main" body

showFront : Expr a -> String
showFront expr =
    let core = runElabM (declMain expr) (ES 0)
    in concatMap showTopLevel core
