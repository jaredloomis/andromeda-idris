module Front

import Data.Vect
import Data.Fin

import Core

%default total

-----------
-- Types --
-----------

Mat : Fin 4 -> Fin 4 -> Type -> Type
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


data Ty : Type -> Type where
    scalar      : Scalar a -> Ty a

    sampler     : (n : Fin 4) -> Ty (Sampler n)
    samplerCube : Ty SamplerCube

    vec         :
        Scalar a -> (n : Fin 4) -> Ty (Vect (finToNat n) a)
    mat         :
        Scalar a -> (n : Fin 4) -> (m : Fin 4) -> Ty (Mat n m a)
    array       :
        Ty a -> Nat -> Ty (List a)

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
    Var     : Name -> Expr a
--        V a -> Expr a
    Literal : Lit a -> Expr a

    LamLit  : (Expr a -> Expr b) -> Expr (a -> b)
--    LamLit  : {A, B : Type} -> (V A -> Expr B) -> Expr (A -> B)
    Lam     : V a -> Expr b -> Expr (a -> b)
      
    (:$)    : Expr (a -> b) -> Expr a -> Expr b

------------------------
-- Operations on Expr --
------------------------

typeOf : Expr a -> {auto ty : Ty a} -> Ty a
typeOf _ {ty} = ty

partial freeIn' : Name -> Expr a -> Bool
freeIn' n (Var n')    = n == n'
freeIn' n (Literal _) = False
freeIn' n (LamLit _)  = False
freeIn' n (Lam _ body) = freeIn' n body
freeIn' n (f :$ x) = freeIn' n f || freeIn' n x

freeIn : Name -> Expr a -> Bool
freeIn n expr = assert_total (freeIn' n expr)

partial betaReduce' : Expr a -> Expr a 
betaReduce' v@(Front.Var _)       = v
betaReduce' l@(Literal _)   = l
betaReduce' (Lam var body)  = Lam var (betaReduce' body)
betaReduce' l@(LamLit _)    = l
betaReduce' (LamLit f :$ x) = f x
    {-
    let name = "normVar_wakawakaa__"
        x'   = betaReduce x
        tyN  = typeOf x'
    in Lam (MkV tyN name) (f $ MkV tyN name) :$ x'
    -}
betaReduce' (f :$ x) = betaReduce' f :$ betaReduce' x

betaReduce : Expr a -> Expr a 
betaReduce expr = assert_total (betaReduce' expr)
