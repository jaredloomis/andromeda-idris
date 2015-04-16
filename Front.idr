module Front

import Data.Vect
import Data.Fin

import Core

%default total

-----------
-- Utils --
-----------

exist : (p -> Type) -> Type
exist {p} ty = Sigma p (\a => ty a)

-----------
-- Types --
-----------

Mat : Nat -> Nat -> Type -> Type
Mat n m a = Vect n (Vect m a)

data Sampler : Fin 4 -> Type where

data SamplerCube : Type where

data Scalar = void | bool | int | uint | float

interpScalar : Scalar -> Type
interpScalar void  = ()
interpScalar bool  = Bool
interpScalar int   = Int
interpScalar uint  = Nat
interpScalar float = Float

----------
-- Type --
----------

infixr 3 ~>
data Ty =
    scalar Scalar
  | sampler (Fin 4)
  | samplerCube
  | vec Nat Scalar
  | mat Nat Nat Scalar
  | array Nat Ty
  | (~>) Ty Ty

interpTy : Ty -> Type
interpTy (scalar s)  = interpScalar s
interpTy (sampler n) = Sampler n
interpTy samplerCube = SamplerCube
interpTy (vec n s)   = Vect n (interpScalar s)
interpTy (mat n m s) = Mat n m (interpScalar s)
interpTy (array n t) = Vect n (interpTy t)
interpTy (a ~> b)    = interpTy a -> interpTy b

----------
-- Expr --
----------

data V : Ty -> Type where
    MkV : (a : Ty) -> Name -> V a

data Lit : Ty -> Type where
    LitFlt   : Float -> Lit (scalar float)
    LitBool  : Bool  -> Lit (scalar bool)
    LitInt   : Int   -> Lit (scalar int)
    LitUInt  : Nat   -> Lit (scalar uint)

    LitCode  : (a : Ty) -> Code -> Lit a

    PreUnOp  : (a : Ty) -> (b : Ty) -> Name -> Lit (a ~> b)
    PostUnOp : (a : Ty) -> (b : Ty) -> Name -> Lit (a ~> b)
    BinOp    : (a : Ty) -> (b : Ty) -> (c : Ty) ->
               Name -> Lit (a ~> b ~> c)

infixl 2 :$
data Expr : Ty -> Type where
    Ref     : Name -> Expr a
--            V a  -> Expr a
    Literal : Lit a -> Expr a

    LamLit  : Qualifier -> (a : Ty) -> (V a -> Expr b) -> Expr (a ~> b)
    Lam     : Qualifier -> V a -> Expr b -> Expr (a ~> b)
      
    (:$)    : Expr (a ~> b) -> Expr a -> Expr b

Var : V a -> Expr a
Var (MkV _ name) = Ref name

syntax "/\\" {x} ":" [q] "," [ty] "=>" [y] =
    LamLit q ty $ \var => let x = Var var in y

--------------------
-- Expr Instances --
--------------------

instance Num (Expr (scalar int)) where
    a + b = Literal (BinOp _ _ _ "+") :$ a :$ b
    a - b = Literal (BinOp _ _ _ "-") :$ a :$ b
    a * b = Literal (BinOp _ _ _ "*") :$ a :$ b
    abs a = Literal (LitCode _ "abs") :$ a
    fromInteger i = Literal (LitInt (fromInteger i))
instance Num (Expr (scalar uint)) where
    a + b = Literal (BinOp _ _ _ "+") :$ a :$ b
    a - b = Literal (BinOp _ _ _ "-") :$ a :$ b
    a * b = Literal (BinOp _ _ _ "*") :$ a :$ b
    abs a = Literal (LitCode _ "abs") :$ a
    fromInteger i = Literal (LitUInt (fromInteger i))
instance Num (Expr (scalar float)) where
    a + b = Literal (BinOp _ _ _ "+") :$ a :$ b
    a - b = Literal (BinOp _ _ _ "-") :$ a :$ b
    a * b = Literal (BinOp _ _ _ "*") :$ a :$ b
    abs a = Literal (LitCode _ "abs") :$ a
    fromInteger i = Literal (LitFlt (fromInteger i))

------------
-- Assign --
------------

infixr 2 :=
data Assign : Type where
    (:=) : Expr a -> Expr a -> Assign
