module StdLib

import Data.Fin

import Core
import Front
import FrontToCore

%default total

infixl 9 *#
(*#) : Expr a -> Expr b -> Expr c
a *# b = Literal (BinOp "*") :$ a :$ b

infixl 3 :=
(:=) : V a -> Expr a -> Expr ()
(:=) var val =
    Literal (BinOp "=") :$ Var var :$ val

-------------------
-- Vec appending --
-------------------

class VecConstruct a b c | a, b where
    vec : Expr a -> Expr b -> Expr c

instance VecConstruct (Vect n ty) (Vect m ty) (Vect (n+m) ty) where
    vec {n} {m} a b =
        Literal (LitCode $ "vec" ++ show (n+m)) :$ a :$ b
instance VecConstruct ty (Vect n ty) (Vect (n+1) ty) where
    vec {n} s v =
        Literal (LitCode $ "vec" ++ show (n+1)) :$ s :$ v
instance VecConstruct (Vect n ty) ty (Vect (n+1) ty) where
    vec {n} v s =
        Literal (LitCode $ "vec" ++ show (n+1)) :$ v :$ s

glPosition : Expr (Vect 3 Float) ->
             Expr (Mat 4 4 Float) ->
             Expr (Vect 4 Float)
glPosition vertPos_modelSpace mvp =
    mvp *# vec vertPos_modelSpace (Literal (LitFlt 1))

myMain : Expr (Vect 3 Float ->
               Vect 3 Float ->
               Mat 4 4 Float ->
               ())
myMain =
    /\ vertPos_modelSpace : inQ      , vec 3 float   =>
    /\ vertexColor        : inQ      , vec 3 float   =>
    /\ mvp                : uniformQ , mat 4 4 float =>
    MkV (vec 4 float) "gl_Position" := glPosition vertPos_modelSpace mvp

mainStr : String
mainStr = showFront myMain
