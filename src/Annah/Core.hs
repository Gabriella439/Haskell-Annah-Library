{-# LANGUAGE OverloadedStrings  #-}

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
import qualified Morte.Core as M
import Prelude hiding (const, pi)

import Annah.Pretty
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
