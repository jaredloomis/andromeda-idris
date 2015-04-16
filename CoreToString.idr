module CoreToString

import Data.Fin

import Core

%default total

----------
-- Util --
----------

intercalateStr : String -> List String -> String
intercalateStr sep (xi :: xs) = foldl (\accum, x => accum ++ sep ++ x) xi xs
intercalateStr _   _          = ""

pad : String -> String
pad ""  = ""
pad str = str ++ " "

infixr 5 <++>
(<++>) : String -> String -> String
a <++> b = pad a ++ b

----------
-- Type --
----------

showScalar : CScalar -> String
showScalar CFloat  = "float"
showScalar CDouble = "double"
showScalar CInt    = "int"
showScalar CUInt   = "uint"
showScalar CBool   = "bool"
showScalar CVoid   = "void"

scalarPrefix : CScalar -> String
scalarPrefix CFloat  = ""
scalarPrefix CDouble = "d"
scalarPrefix CInt    = "i"
scalarPrefix CUInt   = "u"
scalarPrefix CBool   = "b"
scalarPrefix CVoid   =
    "/* ERROR: Tried to create a conglomerate of void */"

showType : CType -> String
showType (CScalarTy sc) = showScalar sc
showType (CVec ty n) =
    scalarPrefix ty ++
    "vec" ++ show (finToNat n)
showType (CMat ty n m) =
    scalarPrefix ty ++ "mat" ++
    show (finToNat n) ++ "x" ++ show (finToNat m)
showType (CArray ty n) =
    showType ty ++ "[" ++ show n ++ "]"
showType (CSampler n) = "sampler" ++ show (finToNat n) ++ "D"
showType CSamplerCube = "samplerCube"
showType (CProduct tyA tyB) = "Pair" -- TODO

----------
-- Expr --
----------

showExpr : CExpr -> String
showExpr (CVar name) = name
showExpr (CLit (CLitCode c)) = c
showExpr (CLit (CLitFlt f)) = show f
showExpr (CLit (CLitInt i)) = show i
showExpr (CLit (CLitUInt u)) = show u
showExpr (CLit (CLitBool b)) = show b
showExpr (CLit (CBinOp op)) = op
showExpr (CLit (CPreUnOp op)) = op
showExpr (CLit (CPostUnOp op)) = op
showExpr (CLit CPair) = "Pair"
showExpr e@(CApp (CLit (CBinOp op)) [x, y]) =
    "(" ++ showExpr (assert_smaller e x) ++ ")" ++ op ++
    "(" ++ showExpr (assert_smaller e y) ++ ")"
showExpr e@(CApp (CLit (CPreUnOp op)) [x]) =
    op ++ "(" ++ showExpr (assert_smaller e x) ++ ")"
showExpr e@(CApp (CLit (CPostUnOp op)) [x]) =
    "(" ++ showExpr (assert_smaller e x) ++ ")" ++ op
showExpr e@(CApp f xs) =
    showExpr f ++
    "(" ++
    intercalateStr ", " (map (showExpr . assert_smaller e) xs)
    ++ ")"

---------------
-- Qualifier --
---------------

showStorageQualifier : StorageQualifier -> String
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

showLayoutQualifier : LayoutQualifier -> String
showLayoutQualifier [] = ""
showLayoutQualifier xs =
    "layout(" ++
    intercalateStr ", " (map showLayoutQual xs)
    ++ ")"
  where
    showLayoutQual : LayoutQual -> String
    showLayoutQual (attrib , Just val) =
        attrib ++ " = " ++ show val
    showLayoutQual (attrib , Nothing)  =
        attrib

showInterpolationQualifier : InterpolationQualifier -> String
showInterpolationQualifier Flat             = "flat"
showInterpolationQualifier NoPerspective    = "noperspective"
showInterpolationQualifier Smooth           = "smooth"

showQualifier : Qualifier -> String
showQualifier (MkQualifier layout storage interpolation) =
    maybe "" showLayoutQualifier        layout  <++>
    maybe "" showStorageQualifier       storage <++>
    maybe "" showInterpolationQualifier interpolation

-------------
-- FullVar --
-------------

showFullVar : FullVar -> String
showFullVar ((ty , qual) , name) =
    showQualifier qual <++> showType ty <++> name

---------------
-- Statement --
---------------

showStatement : CStatement -> String
showStatement (DoExpr expr)      = showExpr expr ++ ";\n"
showStatement e@(SequenceStmt a b) =
    showStatement (assert_smaller e a) ++
    showStatement (assert_smaller e b)
showStatement EmptyStmt = ""
showStatement (DefineStmt (CDefine ty name expr)) =
    showType ty <++> name <++> "=" <++>
    showExpr expr ++ ";\n"
showStatement (Assign to from) =
    to <++> "=" <++> showExpr from ++ ";\n"
showStatement e@(If b t Nothing) =
    "if(" ++ showExpr b ++ ") {\n" ++
        showStatement (assert_smaller e t) ++
    "}"
showStatement e@(If b t (Just f)) =
    "if(" ++ showExpr b ++ ") {\n" ++
        showStatement (assert_smaller e t) ++
    "} else {\n" ++
        showStatement (assert_smaller e f) ++
    "}"
showStatement (Switch _ _)      = "/* USED SWITCH. TODO */"
showStatement (While _ _)       = "/* USED WHILE. TODO */"
showStatement (DoWhile _ _)     = "/* USED DOWHILE. TODO */"
showStatement (For _ _ _ _)     = "/* USED FOR. TODO */"
showStatement Continue          = "continue;"
showStatement Break             = "break;"
showStatement (Return (Just x)) = "return" <++> showExpr x ++ ";\n"
showStatement (Return Nothing)  = "return;\n"
showStatement Discard           = "discard;\n"

-------------
-- Profile --
-------------

showProfile : Profile -> String
showProfile Core          = "core"
showProfile Compatibility = "compatibility"
showProfile Es            = "es"

--------------
-- TopLevel --
--------------

showTopLevel : CTopLevel -> String
showTopLevel (DeclVar fVar) = showFullVar fVar ++ ";\n"
showTopLevel (DeclFun ty name params body) =
    showType ty <++> name ++ "(" ++
    intercalateStr ", " (map showFullVar params) ++ ") {\n" ++
    showStatement body ++
    "}"
showTopLevel (Version n profile) =
    "#version" <++> show n <++>
    maybe "" showProfile profile
showTopLevel (RawTopLevel str) = str
