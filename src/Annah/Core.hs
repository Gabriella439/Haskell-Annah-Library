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
      module Annah.Syntax

    -- * Core functions
    -- $core
    , exprFromText
    , loadExpr
    , desugar
    , resugarTypeError
    , resugar
    , prettyExpr

    -- * Re-exports
    , Identity
    ) where

import Data.Functor.Identity (Identity)

import Annah.Error
import Annah.Import
import Annah.Parser
import Annah.Pretty
import Annah.Sugar
import Annah.Syntax

import qualified Morte.Core as M

{- $core
    The typical workflow is:

    * You parse a `Text` source using `exprFromText`

    * You load all external imports using `loadExpr`

    * You `desugar` the Annah expression to Morte

    * You type-check the Morte expression using `M.typeOf`

    * If there is a type error, resugar the type error using `resugarTypeError`

    * You `M.normalize` the Morte expression

    * You `resugar` the Morte expression back to Annah

    * You pretty-print the Annah expression using `prettyExpr`
-}
