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

-- Normalizing --

subst : Name -> Expr b -> Expr a -> Expr a
subst name s (Lam q var body) =
    Lam q var (subst name s body)
subst name s (f :$ x) =
    subst name s f :$ subst name s x
subst name s e@(Ref name') =
    if name == name' then believe_me s else e
subst _ _ e = e

normalize : Expr a -> ElabM (Expr a)
normalize e@(Lam q (MkV _ name) f :$ x) = do
    f' <- normalize f
    x' <- normalize x
    normalize $ assert_smaller e (subst name x' f')
normalize e@(LamLit q ty f) = do
    name <- freshName
    let expr = f $ MkV ty name
    expr' <- normalize expr
    normalize (assert_smaller e $ Lam q (MkV ty name) expr')
normalize (Lam q var body) = do
    body' <- normalize body
    return $ Lam q var body'
normalize (f :$ x) = do
    f' <- normalize f
    x' <- normalize x
    return $ f' :$ x'
normalize e = return e

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

declFun : Name -> Expr a -> ElabM (List CTopLevel)
declFun nameStr expr = do
    expr' <- normalize expr
    let (params, (_ ** body)) = collectParams expr'
    (tops, body') <- genBody (assert_smaller expr body)
    let decl = DeclFun (CScalarTy CVoid)
                       nameStr
                       params
                       (Return (Just body'))
    return $ tops ++ [decl]
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

    genBody : Expr a -> ElabM (List CTopLevel, CExpr)
    genBody (Ref name)  = return ([], CVar name)
    genBody (Literal x) = return ([], CLit (litToCore x))
    genBody (LamLit _ _ _) =
        return ([], CVar "error: see FrontToCore.idr")
    genBody (Lam q var body) = do
        let name' = nameStr ++ "_prime"
        fun <- declFun name' (Lam q var body)
        return (fun, CVar name')
    genBody (f :$ x) = do
        (tf, f') <- genBody f
        (tx, x') <- genBody x
        return (tf ++ tx, CApp' f' x')

declMain : Expr a -> ElabM (List CTopLevel)
declMain expr = do
    expr' <- normalize expr
    (varDecls, (_ ** body)) <- declVars expr'
    mainDecls <- declFun "main" body
    return $ varDecls ++ mainDecls

showFront : Expr a -> String
showFront expr =
    let core = runElabM (declMain expr) (ES 0)
    in concatMap showTopLevel core
