{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing logic for syntax trees

module Annah.Pretty (
    -- * Pretty printing
      prettyExpr
    , buildExpr
    ) where

import Data.Functor.Identity (Identity, runIdentity)
import Data.List (intersperse)
import Data.Monoid ((<>), mempty, mconcat)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (Builder, fromLazyText, toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Morte.Core as M

import Annah.Sugar (desugar)
import Annah.Syntax

{-| Pretty-print an expression

    The result is a syntactically valid Annah program
-}
prettyExpr :: Expr Identity -> Text
prettyExpr = toLazyText . buildExpr

buildArg :: Arg Identity -> Builder
buildArg (Arg x _A) = "(" <> fromLazyText x <> " : " <> buildExpr _A <> ")"

buildProductTypeField :: ProductTypeField Identity -> Builder
buildProductTypeField (ProductTypeField x _A) =
    if x == "_"
    then buildExpr _A
    else fromLazyText x <> " : " <> buildExpr _A

buildProductTypeSectionField :: ProductTypeSectionField Identity -> Builder
buildProductTypeSectionField (TypeField a   ) = buildProductTypeField a
buildProductTypeSectionField  EmptyTypeField  = mempty

buildProductValueField :: ProductValueField Identity -> Builder
buildProductValueField (ProductValueField a b) =
    buildExpr a <> " : " <> buildExpr b

buildProductValueSectionField :: ProductValueSectionField Identity -> Builder
buildProductValueSectionField (ValueField     a) = buildProductValueField a
buildProductValueSectionField (TypeValueField t) = buildExpr t
buildProductValueSectionField  EmptyValueField   = mempty

buildFamily :: Family Identity -> Builder
buildFamily (Family gs ts)
    =   "given "
    <>  mconcat (map (\g -> fromLazyText g <> " ") gs)
    <>  mconcat (map buildType ts)

buildType :: Type Identity -> Builder
buildType (Type t f ds)
    =   "type "
    <>  fromLazyText t
    <>  " fold "
    <>  fromLazyText f
    <>  " "
    <>  mconcat (map buildData ds)

buildData :: Data Identity -> Builder
buildData (Data d args)
    =   "data "
    <>  fromLazyText d
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)

buildLet :: Let Identity -> Builder
buildLet (Let n args t r)
    =   "let "
    <>  fromLazyText n
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)
    <>  ": "
    <>  buildExpr t
    <>  " = "
    <>  buildExpr r
    <>  " "

buildMultiLambda :: MultiLambda Identity -> Builder
buildMultiLambda (MultiLambda args e)
    =   "λ"
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)
    <>  " → "
    <> buildExpr e
-- TODO: Fix this to use precedence correctly for unused case

-- | Render a pretty-printed expression as a `Builder`
buildExpr :: Expr Identity -> Builder
buildExpr = go 0
  where
    go :: Int -> Expr Identity -> Builder
    go prec e = case e of
        Const c             -> M.buildConst c
        Var x               -> M.buildVar x
        Lam x _A b          -> quoteAbove 1 (
                "λ"
            <>  (if M.used x (desugar b)
                 then "(" <> fromLazyText x <> " : " <>  go 1 _A <>  ")"
                 else go 3 _A)
            <>  " → "
            <>  go 1 b )
        Pi  x _A b          -> quoteAbove 1 (
                (if M.used x (desugar b)
                 then "∀(" <> fromLazyText x <> " : " <> go 1 _A <> ")"
                 else go 2 _A )
            <>  " → "
            <>  go 1 b )
        App f a             -> quoteAbove 2 (go 2 f <> " " <> go 3 a)
        Annot s t           -> quoteAbove 0 (go 2 s <> " : " <> go 1 t)
        MultiLam m          -> quoteAbove 1 (buildMultiLambda m)
        Lets ls e'          -> quoteAbove 1 (
            mconcat (map buildLet ls) <> "in " <> go 1 e' )
        Fam f e'            -> quoteAbove 1 (buildFamily f <> "in " <> go 1 e')
        Natural n           -> decimal n
        ProductValue fields ->
                "("
            <>  mconcat (intersperse "," (map buildProductValueSectionField fields))
            <>  ")"
        ProductType args    ->
                "{"
            <>  mconcat (intersperse "," (map buildProductTypeSectionField args))
            <>  "}"
        Import m            -> go prec (runIdentity m)
      where
        quoteAbove :: Int -> Builder -> Builder
        quoteAbove n b = if prec > n then "(" <> b <> ")" else b
