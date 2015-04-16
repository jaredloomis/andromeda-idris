module StdLib

import Data.Fin

import Core
import Front
import FrontToCore

%default total

----------------------------------
-- Heterogeneous multiplication --
----------------------------------

class HeteroMult a b c | a, b where

-- vec * vec = vec
instance HeteroMult (Vect n a) (Vect n a) (Vect n a) where
-- mat * mat = mat
instance HeteroMult (Mat j n ty) (Mat n k ty) (Mat j k ty) where
-- mat * vec = vec
instance HeteroMult (Mat n m a) (Vect n a) (Vect n a) where
instance HeteroMult (Vect n a) (Mat n m a) (Vect n a) where
-- vec * scalar = vec
instance HeteroMult (Vect n a) a (Vect n a) where
instance HeteroMult a (Vect n a) (Vect n a) where
-- mat * scalar = mat
instance HeteroMult a (Mat n m a) (Mat n m a) where
instance HeteroMult (Mat n m a) a (Mat n m a) where
-- float * integral = float
instance HeteroMult Float Int Float where
instance HeteroMult Int Float Float where
instance HeteroMult Float Nat Float where
instance HeteroMult Nat Float Float where
-- scalar * scalar = scalar
instance HeteroMult Float Float Float where
instance HeteroMult Int Int Int where
instance HeteroMult Nat Nat Nat where

infixl 9 *#
(*#) : HeteroMult a b c => Expr a -> Expr b -> Expr c
(*#) x y = Literal (BinOp "*") :$ x :$ y

----------------
-- Assignment --
----------------

infixr 2 :=
(:=) : Expr a -> Expr a -> Expr ()
(:=) var val = Literal (BinOp "=") :$ var :$ val

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
(@) : Expr (Vect n a) -> Swizzle n t -> Expr (Vect t a)
(@) expr swiz =
    Literal (PostUnOp $ "." ++ showSwizzle swiz) :$ expr

------

glPosition : Vect 3 Float ~> Mat 4 4 Float ~|> Vect 4 Float
glPosition vertPos_modelSpace mvp =
    mvp *# vec vertPos_modelSpace (Literal (LitFlt 1))

myMain : Expr (Vect 3 Float -> Mat 4 4 Float -> ())
myMain =
    /\ vertPos_modelSpace : inQ      , vec 3 float   =>
    /\ mvp                : uniformQ , mat 4 4 float =>
    Ref "gl_Position" :=
        glPosition vertPos_modelSpace mvp @ X & Y & Z & W

mainStr : String
mainStr = showFront myMain
