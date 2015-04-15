module Front

import Data.Vect
import Data.Fin

import Core

%default total

-----------
-- Utils --
-----------

exist : (Type -> Type) -> Type
exist ty = Sigma Type (\a => ty a)

-----------
-- Types --
-----------

Mat : Fin 5 -> Fin 5 -> Type -> Type
Mat n m a = Vect (finToNat n) (Vect (finToNat m) a)

data Sampler : Fin 4 -> Type where

data SamplerCube : Type where

data Scalar : Type -> Type where
    void  : Scalar ()

    bool  : Scalar Bool
    int   : Scalar Int
    uint  : Scalar Nat
    float : Scalar Float

----------
-- Type --
----------

infixr 5 ~>
data Ty : Type -> Type where
    scalar      : Scalar a -> Ty a

    sampler     : (n : Fin 4) -> Ty (Sampler n)
    samplerCube : Ty SamplerCube

    vec         :
        (n : Fin 5) -> Scalar a -> Ty (Vect (finToNat n) a)
    mat         :
        (n : Fin 5) -> (m : Fin 5) -> Scalar a  -> Ty (Mat n m a)
    array       :
        Nat -> Ty a -> Ty (List a)

    (&)         : Ty a -> Ty b -> Ty (a,   b)
    (~>)        : Ty a -> Ty b -> Ty (a -> b)

    -- | Unneeded/Unused/Erased type
    Any : Ty a



----------
-- Expr --
----------

data V : Type -> Type where
    MkV : Ty a -> Name -> V a

data Lit : Type -> Type where
    LitFlt   : Float -> Lit Float
    LitBool  : Bool  -> Lit Bool
    LitInt   : Int   -> Lit Int
    LitUInt  : Nat   -> Lit Nat

    LitCode  : Code  -> Lit a

    PreUnOp  : Name  -> Lit (a -> b)
    PostUnOp : Name  -> Lit (a -> b)
    BinOp    : Name  -> Lit (a -> b -> c)

    Pair     : Lit (a -> b -> (a, b))

infixl 2 :$
data Expr : Type -> Type where
    Ref     : Name -> Expr a
--            V a  -> Expr a
    Literal : Lit a -> Expr a

    LamLit  : Qualifier -> Ty a -> (V a -> Expr b) -> Expr (a -> b)
    Lam     : Qualifier -> V a -> Expr b -> Expr (a -> b)
      
    (:$)    : Expr (a -> b) -> Expr a -> Expr b

Var : V a -> Expr a
Var (MkV _ name) = Ref name

syntax "/\\" {x} ":" [q] "," [ty] "=>" [y] =
    LamLit q ty $ \var => let x = Var var in y

--------------------
-- Expr Instances --
--------------------

instance Num (Expr Int) where
    a + b = Literal (BinOp "+") :$ a :$ b
    a - b = Literal (BinOp "-") :$ a :$ b
    a * b = Literal (BinOp "*") :$ a :$ b
    abs a = Literal (LitCode "abs") :$ a
    fromInteger i = Literal (LitInt (fromInteger i))
instance Num (Expr Nat) where
    a + b = Literal (BinOp "+") :$ a :$ b
    a - b = Literal (BinOp "-") :$ a :$ b
    a * b = Literal (BinOp "*") :$ a :$ b
    abs a = Literal (LitCode "abs") :$ a
    fromInteger i = Literal (LitUInt (fromInteger i))
instance Num (Expr Float) where
    a + b = Literal (BinOp "+") :$ a :$ b
    a - b = Literal (BinOp "-") :$ a :$ b
    a * b = Literal (BinOp "*") :$ a :$ b
    abs a = Literal (LitCode "abs") :$ a
    fromInteger i = Literal (LitFlt (fromInteger i))

------------------------
-- Operations on Expr --
------------------------

freeIn : Name -> Expr a -> Bool
freeIn n (Ref n')    = n == n'
freeIn n (Literal _) = False
freeIn n (LamLit _ _ _)  = False
freeIn n (Lam _ _ body) = freeIn n body
freeIn n (f :$ x) = freeIn n f || freeIn n x
