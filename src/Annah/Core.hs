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

import qualified Morte.Core as M

import Annah.Import
import Annah.Pretty
import Annah.Sugar
import Annah.Syntax
