{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DeriveDataTypeable #-}

{-| This module contains the core machinery for the Annah language, which is a
    medium-level distributed language built on top of Morte.

    The main high-level features that Annah does not provide compare to Haskell
    are:

    * type classes

    * type inference

    You cannot type-check or normalize Annah expressions directly.  Instead,
    you:
    
    * `desugar` Annah expressions to Morte,

    * type-check / normalize the Morte expressions using `M.typeOf` and
      `M.normalize`, and

    * `resugar` the Morte expressions back to Annah.

    Annah does everything through Morte for two reasons:

    * to ensure the soundness of type-checking and normalization, and:

    * to interoperate with other languages that compile to Morte.
-}

module Annah.Core (
    -- * Syntax
      M.Var(..)
    , M.Const(..)
    , Arg(..)
    , ProductTypeField(..)
    , ProductValueField(..)
    , Data(..)
    , Type(..)
    , Family(..)
    , Let(..)
    , Expr(..)

    -- * Core functions
    , loadExpr
    , desugar
    , resugar

    -- * Utilities
    , buildExpr
    , prettyExpr
    ) where

import Control.Applicative (pure, (<$>), (<*>))
import Data.Functor.Identity (Identity, runIdentity)
import Data.List (intersperse)
import Data.Monoid (Monoid(..), (<>))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import qualified Morte.Core as M
import Prelude hiding (const, pi)

import Annah.Sugar
import Annah.Syntax

-- | Evaluate all `Import`s, leaving behind a pure expression
loadExpr :: Expr IO -> IO (Expr m)
loadExpr (Const c            ) = pure (Const c)
loadExpr (Var v              ) = pure (Var v)
loadExpr (Lam x _A  b        ) = Lam x <$> loadExpr _A <*> loadExpr  b
loadExpr (Pi  x _A _B        ) = Pi  x <$> loadExpr _A <*> loadExpr _B
loadExpr (App f a            ) = App <$> loadExpr f <*> loadExpr a
loadExpr (Annot a _A         ) = Annot <$> loadExpr a <*> loadExpr _A
loadExpr (Lets ls e          ) = Lets <$> mapM loadLet ls <*> loadExpr e
loadExpr (Fam f e            ) = Fam <$> loadFamily f <*> loadExpr e
loadExpr (Natural n          ) = pure (Natural n)
loadExpr (ProductValue fs    ) = ProductValue <$> mapM loadProductValueField fs
loadExpr (ProductType  as    ) = ProductType <$> mapM loadProductTypeField as
loadExpr (ProductAccessor m n) = pure (ProductAccessor m n)
loadExpr (Import io          ) = io >>= loadExpr

loadFamily :: Family IO -> IO (Family m)
loadFamily (Family as bs) = Family as <$> mapM loadType bs

loadType :: Type IO -> IO (Type m)
loadType (Type a b cs) = Type a b <$> mapM loadData cs

loadData :: Data IO -> IO (Data m)
loadData (Data a bs) = Data a <$> mapM loadArg bs

loadLet :: Let IO -> IO (Let m)
loadLet (Let f args _B b) =
    Let f <$> mapM loadArg args <*> loadExpr _B <*> loadExpr b

loadArg :: Arg IO -> IO (Arg m)
loadArg (Arg x _A) = Arg x <$> loadExpr _A

loadProductTypeField :: ProductTypeField IO -> IO (ProductTypeField m)
loadProductTypeField (ProductTypeField x _A) =
    ProductTypeField x <$> loadExpr _A

loadProductValueField :: ProductValueField IO -> IO (ProductValueField m)
loadProductValueField (ProductValueField f t) =
    ProductValueField <$> loadExpr f <*> loadExpr t

buildArg :: Arg Identity -> Builder
buildArg (Arg x _A) = "(" <> fromLazyText x <> " : " <> buildExpr _A <> ")"

buildProductTypeField :: ProductTypeField Identity -> Builder
buildProductTypeField (ProductTypeField x _A) =
    if x == "_"
    then buildExpr _A
    else fromLazyText x <> " : " <> buildExpr _A

buildProductValueField :: ProductValueField Identity -> Builder
buildProductValueField (ProductValueField a b) = buildExpr a <> " : " <> buildExpr b

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

-- | Render a pretty-printed expression as a `Builder`
buildExpr :: Expr Identity -> Builder
buildExpr = go 0
  where
    go :: Int -> Expr Identity -> Builder
    go prec e = case e of
        Const c             -> M.buildConst c
        Var x               -> M.buildVar x
        Lam x _A b          -> quoteAbove 1 (
                "λ("
            <>  fromLazyText x
            <>  " : "
            <>  go 1 _A
            <>  ") → "
            <>  go 1 b )
        Pi  x _A b          -> quoteAbove 1 (
                (if M.used x (desugar b)
                 then "∀(" <> fromLazyText x <> " : " <> go 1 _A <> ")"
                 else go 2 _A )
            <>  " → "
            <>  go 1 b )
        App f a             -> quoteAbove 2 (go 2 f <> " " <> go 3 a)
        Annot s t           -> quoteAbove 0 (go 2 s <> " : " <> go 1 t)
        Lets ls e'          -> quoteAbove 1 (
            mconcat (map buildLet ls) <> "in " <> go 1 e' )
        Fam f e'            -> quoteAbove 1 (buildFamily f <> "in " <> go 1 e')
        Natural n           -> decimal n
        ProductValue fields ->
                "("
            <>  mconcat (intersperse ", " (map buildProductValueField fields))
            <>  ")"
        ProductType args    ->
                "{"
            <>  mconcat (intersperse ", " (map buildProductTypeField args))
            <>  "}"
        ProductAccessor m n -> quoteAbove 3 (decimal m <> " of " <> decimal n)
        Import m            -> go prec (runIdentity m)
      where
        quoteAbove :: Int -> Builder -> Builder
        quoteAbove n b = if prec > n then "(" <> b <> ")" else b

{-| Pretty-print an expression

    The result is a syntactically valid Annah program
-}
prettyExpr :: Expr Identity -> Text
prettyExpr = toLazyText . buildExpr
