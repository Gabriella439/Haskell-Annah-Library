{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing logic for syntax trees

module Annah.Pretty (
    -- * Pretty printing
      prettyExpr
    , Builds(..)
    ) where

import Data.Monoid ((<>), mempty, mconcat)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (Builder, fromText, fromLazyText, toLazyText)
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Morte.Core as M
import Turtle (FilePath, format, fp)
import Prelude hiding (FilePath)

import Annah.Syntax

{-| Pretty-print an expression

    The result is a syntactically valid Annah program
-}
prettyExpr :: Expr FilePath -> Text
prettyExpr = toLazyText . build

-- | Pretty-print a value as a `Builder`
class Builds f where
    build :: f FilePath -> Builder

instance Builds Arg where
    build (Arg "_" _A) =                                   build _A
    build (Arg  x  _A) = "(" <> fromLazyText x <> " : " <> build _A <> ")"

instance Builds ProductTypeField where
    build (ProductTypeField x _A) =
        if x == "_"
        then build _A
        else fromLazyText x <> " : " <> build _A

instance Builds ProductTypeSectionField where
    build (TypeField a   ) = build a
    build  EmptyTypeField  = mempty

instance Builds ProductValueField where
    build (ProductValueField a b) = build a <> " : " <> build b

instance Builds ProductValueSectionField where
    build (ValueField     a) = build a
    build (TypeValueField t) = build t
    build  EmptyValueField   = mempty

instance Builds SumTypeSectionField where
    build  EmptySumTypeField  = mempty
    build (SumTypeField f   ) = build f

instance Builds ListTypeSectionField where
    build  EmptyListTypeSectionField  = mempty
    build (ListTypeSectionField f   ) = build f

instance Builds Family where
    build (Family gs ts)
        =   "given "
        <>  mconcat (map (\g -> build g <> " ") gs)
        <>  mconcat (map build ts)

instance Builds Type where
    build (Type t f ds)
        =   "type "
        <>  fromLazyText t
        <>  " fold "
        <>  fromLazyText f
        <>  " "
        <>  mconcat (map build ds)

instance Builds Data where
    build (Data d args)
        =   "data "
        <>  fromLazyText d
        <>  " "
        <>  mconcat (map (\arg -> build arg <> " ") args)

instance Builds Let where
    build (Let n args t r)
        =   "let "
        <>  fromLazyText n
        <>  " "
        <>  mconcat (map (\arg -> build arg <> " ") args)
        <>  ": "
        <>  build t
        <>  " = "
        <>  build r
        <>  " "

instance Builds Expr where
    build = go 0
      where
        go :: Int -> Expr FilePath -> Builder
        go prec e = case e of
            Const c             -> M.buildConst c
            Var x               -> M.buildVar x
            Lam x _A b          -> quoteAbove 1 (
                    "λ"
                <>  "(" <> fromLazyText x <> " : " <>  go 1 _A <>  ")"
                <>  " → "
                <>  go 1 b )
            Pi  x _A b          -> quoteAbove 1 (
                    (if x /= "_"
                     then "∀(" <> fromLazyText x <> " : " <> go 1 _A <> ")"
                     else go 2 _A )
                <>  " → "
                <>  go 1 b )
            App f a             -> quoteAbove 2 (go 2 f <> " " <> go 3 a)
            Annot s t           -> quoteAbove 0 (go 2 s <> " : " <> go 1 t)
            Lets ls e'          -> quoteAbove 1 (
                mconcat (map build ls) <> "in " <> go 1 e' )
            Fam f e'            -> quoteAbove 1 (build f <> "in " <> go 1 e')
            Natural n           -> decimal n
            ASCII   txt         -> "\"" <> fromLazyText txt <> "\""
            SumConstructor m n  -> decimal m <> "to" <> decimal n
            SumType ts          ->
                    "{0"
                <>  mconcat (map (\t -> "|" <> build t) ts)
                <>  "}"
            ProductValue fields ->
                    "<1"
                <>  mconcat (map (\field -> "," <> build field) fields)
                <>  ">"
            ProductType args    ->
                    "{1"
                <>  mconcat (map (\arg -> "," <> build arg) args)
                <>  "}"
            List t as           ->
                    "[* " <> build t
                <> mconcat (map (\a -> "," <> build a) as)
                <>  "]"
            ListType t          -> "[" <> build t <> "]"
            Path c oms o0       ->
                    "[. " <> build c
                <> mconcat
                    (map (\(o, m) -> " (|" <> build o <> "|) " <> build m) oms)
                <> " (|" <> build o0 <> "|)]"
            Import m            -> "#" <> fromText (format fp m)
          where
            quoteAbove :: Int -> Builder -> Builder
            quoteAbove n b = if prec > n then "(" <> b <> ")" else b
