module StdLib

import Data.Fin

import Core
import Front
import FrontToCore

%default total

----------------------------------
-- Heterogeneous multiplication --
----------------------------------

class HeteroMult (a : Ty) (b : Ty) (c : Ty) | a, b where

-- vec * vec = vec
instance HeteroMult (vec n a) (vec n a) (vec n a) where
-- mat * mat = mat
instance HeteroMult (mat j n ty) (mat n k ty) (mat j k ty) where
-- mat * vec = vec
{-
instance HeteroMult (mat n m a) (vec n a) (vec n a) where
instance HeteroMult (vec n a) (mat n m a) (vec n a) where
-}
instance HeteroMult (mat n m a) (vec j a) (vec j a) where
instance HeteroMult (vec j a) (mat n m a) (vec j a) where
-- vec * scalar = vec
instance HeteroMult (vec n a) (scalar a) (vec n a) where
instance HeteroMult (scalar a) (vec n a) (vec n a) where
-- mat * scalar = mat
instance HeteroMult (scalar a) (mat n m a) (mat n m a) where
instance HeteroMult (mat n m a) (scalar a) (mat n m a) where
-- float * integral = float
instance HeteroMult (scalar float) (scalar int) (scalar float) where
instance HeteroMult (scalar int) (scalar float) (scalar float) where
instance HeteroMult (scalar float) (scalar uint) (scalar float) where
instance HeteroMult (scalar uint) (scalar float) (scalar float) where
-- scalar * scalar = scalar
instance HeteroMult (scalar float) (scalar float) (scalar float) where
instance HeteroMult (scalar int) (scalar int) (scalar int) where
instance HeteroMult (scalar uint) (scalar uint) (scalar uint) where

infixl 9 *#
(*#) : HeteroMult a b c => Expr a -> Expr b -> Expr c
(*#) x y = Literal (BinOp _ _ _ "*") :$ x :$ y

----------------
-- Assignment --
----------------
{-
infixr 2 :=
(:=) : Expr a -> Expr a -> Expr ()
(:=) var val = Literal (BinOp "=") :$ var :$ val
-}
-------------------
-- Vec appending --
-------------------

infixr 8 &#
class VecConstruct (a : Ty) (b : Ty) (c : Ty) | a, b where
    (&#) : Expr a -> Expr b -> Expr c

instance VecConstruct (vec n ty) (vec m ty) (vec (n+m) ty) where
    (&#) {n} {m} a b =
        Literal (LitCode _ $ "vec" ++ show (n+m)) :$ a :$ b
instance VecConstruct (scalar ty) (vec n ty) (vec (S n) ty) where
    (&#) {n} s v =
        Literal (LitCode _ $ "vec" ++ show (S n)) :$ s :$ v
instance VecConstruct (vec n ty) (scalar ty) (vec (S n) ty) where
    (&#) {n} v s =
        Literal (LitCode _ $ "vec" ++ show (S n)) :$ v :$ s

-------------------
-- Vec swizzling --
-------------------

infixr 6 &
-- | Swizzle (miniumum length of initial vec)
--           (length of result vec)
data Swizzle : Nat -> Nat -> Type where
    X   : Swizzle (S k) 1
    Y   : Swizzle (S (S k)) 1
    Z   : Swizzle (S (S (S k))) 1
    W   : Swizzle (S (S (S (S k)))) 1
    (&) : Swizzle f t1 -> Swizzle f t2 ->
          Swizzle f (t1 + t2)

showSwizzle : Swizzle f t -> String
showSwizzle X       = "x"
showSwizzle Y       = "y"
showSwizzle Z       = "z"
showSwizzle W       = "w"
showSwizzle (a & b) = showSwizzle a ++ showSwizzle b

infixr 3 @
(@) : Expr (vec n a) -> Swizzle n t -> Expr (vec t a)
(@) expr swiz =
    Literal (PostUnOp _ _ $ "." ++ showSwizzle swiz) :$ expr

------

positionF : Expr (vec 3 float) -> Expr (mat 4 4 float) ->
            Expr (vec 4 float)
positionF vertPos_modelSpace mvp =
    mvp *# vertPos_modelSpace &# Literal (LitFlt 1)

positionExpr : Expr (vec 3 float ~> mat 4 4 float ~> vec 4 float)
positionExpr =
    /\ vertPos_modelSpace : inQ      , vec 3 float   =>
    /\ mvp                : uniformQ , mat 4 4 float =>
    positionF vertPos_modelSpace mvp @ X & Y & Z & W

posStr : String
posStr = showFront positionExpr

position' : List Assign
position' = [Ref "gl_Position" := positionExpr,
             Ref "position"    := positionExpr]

posStr' : String
posStr' = showAssigns position'
