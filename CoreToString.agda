{-# OPTIONS --no-termination-check #-}
module CoreToString where

open import Function

open import Data.String
open import Data.List as L hiding (_++_)
open import Data.Float renaming (show to showFlt)
open import Data.Integer renaming (show to showℤ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Bool.Show renaming (show to showBool)
open import Data.Maybe
open import Data.Product

open import Core

----------
-- Util --
----------

intercalate : String → List String → String
intercalate sep (x₁ ∷ xs) = foldl (λ accum x → accum ++ sep ++ x) x₁ xs
intercalate _   _         = ""

test = intercalate ", " ("wasabi" ∷ "onions" ∷ "tomato" ∷ [])

concatStr : List String → String
concatStr = foldr _++_ ""

pad : String -> String
pad ""  = ""
pad str = str ++ " "

infixr 5 _<++>_
_<++>_ : String -> String -> String
a <++> b = pad a ++ b

----------
-- Type --
----------

showScalar : CScalar → String
showScalar CFloat  = "float"
showScalar CDouble = "double"
showScalar CInt    = "int"
showScalar CUInt   = "uint"
showScalar CBool   = "bool"
showScalar CVoid   = "void"

scalarPrefix : CScalar → String
scalarPrefix CFloat  = ""
scalarPrefix CDouble = "d"
scalarPrefix CInt    = "i"
scalarPrefix CUInt   = "u"
scalarPrefix CBool   = "b"
scalarPrefix CVoid   =
    "/* ERROR: Tried to create a conglomerate of void */"

showType : CType → String
showType (CScalarTy sc) = showScalar sc
showType (ty CVec⟦ n ⟧) =
    scalarPrefix ty ++ "vec" ++
    showℕ n
showType (ty CMat⟦ n ⟧⟦ m ⟧) =
    scalarPrefix ty ++ "mat" ++
    showℕ n ++ "x" ++ showℕ m
showType (ty CArray⟦ n ⟧) =
    showType ty ++ "[" ++ showℕ n ++ "]"
showType (CSampler n) = "sampler" ++ showℕ n ++ "D"
showType CSamplerCube = "samplerCube"
showType (CProduct tyA tyB) = "Pair" -- TODO

----------
-- Expr --
----------

showExpr : CExpr → String
showExpr (CVar name) = name
showExpr (CLit (CLitCode c)) = c
showExpr (CLit (CLitFlt f)) = showFlt f
showExpr (CLit (CLitInt i)) = showℤ i
showExpr (CLit (CLitUInt u)) = showℕ u
showExpr (CLit (CLitBool b)) = showBool b
showExpr (CLit (CBinOp op)) = op
showExpr (CLit (CPreUnOp op)) = op
showExpr (CLit (CPostUnOp op)) = op
showExpr (CLit CPair) = "Pair"
showExpr (CApp (CLit (CBinOp op)) (x ∷ y ∷ [])) =
    "(" ++ showExpr x ++ ")" ++ op ++
    "(" ++ showExpr y ++ ")"
showExpr (CApp (CLit (CPreUnOp op)) (x ∷ [])) =
    op ++ "(" ++ showExpr x ++ ")"
showExpr (CApp (CLit (CPostUnOp op)) (x ∷ [])) =
    "(" ++ showExpr x ++ ")" ++ op
showExpr (CApp f xs) =
    showExpr f ++
    "(" ++
    intercalate ", " (L.map showExpr xs)
    ++ ")"

---------------
-- Qualifier --
---------------

showStorageQualifier : StorageQualifier → String
showStorageQualifier Const       = "const"
showStorageQualifier In          = "in"
showStorageQualifier Out         = "out"
showStorageQualifier Uniform     = "uniform"
showStorageQualifier Buffer      = "buffer"
showStorageQualifier CentroidIn  = "centroid in"
showStorageQualifier CentroidOut = "centroid out"
showStorageQualifier SampleIn    = "sample in"
showStorageQualifier SampleOut   = "sample out"
showStorageQualifier PatchIn     = "patch in"
showStorageQualifier PatchOut    = "patch out"

showLayoutQualifier : LayoutQualifier → String
showLayoutQualifier [] = ""
showLayoutQualifier xs =
    "layout(" ++
    intercalate ", " (L.map showLayoutQual xs)
    ++ ")"
  where
    showLayoutQual : LayoutQual → String
    showLayoutQual (attrib , just val) =
        attrib ++ " = " ++ showℕ val
    showLayoutQual (attrib , nothing)  =
        attrib

showInterpolationQualifier : InterpolationQualifier → String
showInterpolationQualifier Flat             = "flat"
showInterpolationQualifier NoPerspective    = "noperspective"
showInterpolationQualifier Smooth           = "smooth"

showQualifier : Qualifier → String
showQualifier (MkQualifier layout storage interpolation) =
    maybe′ showLayoutQualifier        "" layout  <++>
    maybe′ showStorageQualifier       "" storage <++>
    maybe′ showInterpolationQualifier "" interpolation

-------------
-- FullVar --
-------------

showFullVar : FullVar → String
showFullVar ((ty , qual) , name) =
    showQualifier qual <++> showType ty <++> name

---------------
-- Statement --
---------------

showStatement : CStatement → String
showStatement (DoExpr expr)      = showExpr expr ++ ";\n"
showStatement (SequenceStmt a b) = showStatement a ++ showStatement b
showStatement (DefineStmt (CDefine ty name expr)) =
    showType ty <++> name <++> "=" <++>
    showExpr expr ++ ";\n"
showStatement (Assign to from) =
    to <++> "=" <++> showExpr from ++ ";\n"
showStatement (If b t nothing) =
    "if(" ++ showExpr b ++ ") {\n" ++
        showStatement t ++
    "}"
showStatement (If b t (just f)) =
    "if(" ++ showExpr b ++ ") {\n" ++
        showStatement t ++
    "} else {\n" ++
        showStatement f ++
    "}"
showStatement (Switch x x₁)     = "/* USED SWITCH. TODO */"
showStatement (While x x₁)      = "/* USED WHILE. TODO */"
showStatement (DoWhile x x₁)    = "/* USED DOWHILE. TODO */"
showStatement (For x x₁ x₂ x₃)  = "/* USED FOR. TODO */"
showStatement Continue          = "continue;"
showStatement Break             = "break;"
showStatement (Return (just x)) = "return" <++> showExpr x ++ ";\n"
showStatement (Return nothing)  = "return;\n"
showStatement Discard           = "discard;\n"

-------------
-- Profile --
-------------

showProfile : Profile → String
showProfile Core          = "core"
showProfile Compatibility = "compatibility"
showProfile Es            = "es"

--------------
-- TopLevel --
--------------

showTopLevel : CTopLevel → String
showTopLevel (DeclVar fVar) = showFullVar fVar ++ ";\n"
showTopLevel (DeclFun ty name params body) =
    showType ty <++> name ++ "(" ++
    intercalate ", " (L.map showFullVar params) ++ ") {\n" ++
    showStatement body ++
    "}"
showTopLevel (Version n profile) =
    "#version" <++> showℕ n <++>
    maybe′ showProfile "" profile
showTopLevel (RawTopLevel str) = str
