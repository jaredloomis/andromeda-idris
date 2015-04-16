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

Mat : Nat -> Nat -> Type -> Type
Mat n m a = Vect n (Vect m a)

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
        (n : Fin 5) -> Scalar a ->
            Ty (Vect (finToNat n) a)
    mat         :
        (n : Fin 5) -> (m : Fin 5) -> Scalar a  ->
            Ty (Mat (finToNat n) (finToNat m) a)
    array       :
        Nat -> Ty a -> Ty (List a)

--    (&)         : Ty a -> Ty b -> Ty (a,   b)
    arrow       : Ty a -> Ty b -> Ty (a -> b)

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

infixr 3 ~>
(~>) : Type -> Type -> Type
(~>) a b = Expr a -> b

infixr 3 ~|>
(~|>) : Type -> Type -> Type
(~|>) a b = Expr a -> Expr b

infixr 3 ~~>
(~~>) : List Type -> Type -> Type
(~~>) (x::xs) ret = x ~> (xs ~~> ret)
(~~>) []      ret = Expr ret

-------------------
-- Type Checking --
-------------------

typeOfAuto : Expr a -> {auto ty : Ty a} -> Ty a
typeOfAuto _ {ty} = ty

Context : Type
Context = List (Name, exist Ty)

typeLit : Lit a -> Ty a
typeLit (LitFlt _)  = scalar float
typeLit (LitInt _)  = scalar int
typeLit (LitUInt _) = scalar uint
typeLit (LitBool _) = scalar bool
typeLit l           = typeOfAuto (Literal l)

typeWith : Context -> Expr a -> Ty a
typeWith ctx e@(Ref name)     =
    case lookup name ctx of
        Nothing => believe_me $ typeOfAuto e
        Just ty => believe_me   ty
typeWith ctx (Literal l)      = typeLit l
typeWith ctx e@(LamLit _ _ _) = typeOfAuto e
--    normalize e >>= typeWith ctx . assert_smaller e
typeWith ctx (Lam _ (MkV ty name) body) = arrow ty $
    typeWith ((name, (_ ** ty)) :: ctx) body
typeWith ctx (f :$ _) =
    let tyF = typeWith ctx f
    in case tyF of
        arrow _ b => believe_me b
        _         => believe_me tyF

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

------------
-- Assign --
------------

infixr 2 :=
data Assign : Type where
    (:=) : Expr a -> Expr a -> Assign

------------------------
-- Operations on Expr --
------------------------

freeIn : Name -> Expr a -> Bool
freeIn n (Ref n')    = n == n'
freeIn n (Literal _) = False
freeIn n (LamLit _ _ _)  = False
freeIn n (Lam _ _ body) = freeIn n body
freeIn n (f :$ x) = freeIn n f || freeIn n x
