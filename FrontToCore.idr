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

scalarToCore : Scalar -> CScalar
scalarToCore void  = CVoid
scalarToCore bool  = CBool
scalarToCore int   = CInt
scalarToCore uint  = CUInt
scalarToCore float = CFloat

typeToCore : Ty -> CType
typeToCore (scalar scTy) = CScalarTy (scalarToCore scTy)
typeToCore (sampler n) = CSampler n
typeToCore samplerCube = CSamplerCube
typeToCore (vec n scTy) =
    CVec (scalarToCore scTy) n
typeToCore (mat n m scTy) =
    CMat (scalarToCore scTy) n m
typeToCore (array n ty) =
    CArray (typeToCore ty) n
typeToCore (a ~> b) = typeToCore b
typeToCore Any      = CScalarTy CVoid -- Doesn't matter

declVars : Expr a -> ElabM (List CTopLevel, exist Expr)
declVars (LamLit q ty f) = do
    name <- freshName
    let expr = f (MkV ty name)
    (rest, endBody) <- declVars expr
    return (DeclVar ((typeToCore ty, q), name) :: rest, endBody)
declVars (Lam q (MkV ty var) body) = do
    (rest, endBody) <- declVars body
    return (DeclVar ((typeToCore ty, q), var) :: rest, endBody)
declVars expr = return ([], (_ ** expr))

litToCore : Lit a -> CLiteral
litToCore (LitFlt   f)       = CLitFlt   f
litToCore (LitBool  b)       = CLitBool  b
litToCore (LitInt   i)       = CLitInt   i
litToCore (LitUInt  u)       = CLitUInt  u
litToCore (LitCode  _ c)     = CLitCode  c
litToCore (PreUnOp  _ _ o)   = CPreUnOp  o
litToCore (PostUnOp _ _ o)   = CPostUnOp o
litToCore (BinOp    _ _ _ o) = CBinOp   o

exprToCore : Expr a -> ElabM (List CTopLevel, CExpr)
exprToCore (Ref name)  = return ([], CVar name)
exprToCore (Literal x) = return ([], CLit (litToCore x))
exprToCore (LamLit _ _ _) =
    return ([], CVar "error: exprToCore recieved LamLit")
exprToCore (Lam _ _ _) =
    return ([], CVar "error: exprToCore recieved Lam")
{-
exprToCore (Lam q var body) = do
    name <- freshName
    fun <- declFun name (Lam q var body)
    return (fun, CVar name)
    -}
exprToCore (f :$ x) = do
    (tf, f') <- exprToCore f
    (tx, x') <- exprToCore x
    return (tf ++ tx, CApp' f' x')

declFun : Name -> Expr a -> ElabM (List CTopLevel)
declFun {a=fTy} nameStr expr = do
    expr' <- normalize expr
    let (params, (_ ** body)) = collectParams expr'
    (tops, body') <- exprToCore (assert_smaller expr body)
    retTy <- coreTy body
    let decl = DeclFun retTy
                       nameStr
                       params
                       (funStatement retTy body')
    return $ tops ++ [decl]
  where
    funStatement : CType -> CExpr -> CStatement
    funStatement (CScalarTy CVoid) expr = DoExpr expr
    funStatement _                 expr = Return (Just expr)

    coreTy : Expr a -> ElabM CType
    coreTy {a} e = return $ typeToCore a

    collectParams :
        Expr a -> (List FullVar, exist Expr)
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

elabAssign : Assign -> ElabM (List CTopLevel, List CTopLevel, CStatement)
elabAssign ((:=) {a = ty} (Ref name) expr) = do
    expr' <- normalize expr
    (varDecls, (_ ** val)) <- declVars expr'

    topDecls <- if not ("gl_" `isPrefixOf` name)
        then do
            let cty = typeToCore ty
            return (the (List CTopLevel) [DeclVar ((cty, outQ), name)])
        else return []
    (tops, core) <- exprToCore val

    return (varDecls, topDecls ++ tops, Assign name core)
elabAssign _ = return ([], [], EmptyStmt)

collectAssigns : List Assign ->
                 ElabM (List CTopLevel, List CTopLevel, CStatement)
collectAssigns (x :: xs) = do
    (v,  t,  s)  <- elabAssign x
    (v', t', s') <- collectAssigns xs
    return (v ++ v', t ++ t', SequenceStmt s s')
collectAssigns [] = return ([], [], EmptyStmt)

declAssigns : List Assign -> Name -> ElabM (List CTopLevel)
declAssigns xs name = do
    (vars, tops, stmt) <- collectAssigns xs

    let decl = DeclFun (CScalarTy CVoid) name [] stmt
    return (vars ++ tops ++ [decl])

showAssigns : List Assign -> String
showAssigns xs =
    let core = runElabM (declAssigns xs "main") (ES 0)
    in concatMap showTopLevel core

