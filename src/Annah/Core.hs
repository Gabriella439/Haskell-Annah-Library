{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports #-}

{-| This module contains the core machinery for the Annah language, which is a
    medium-level language that desugars to Morte.

    The main high-level features that Annah does not provide compared to Haskell
    are:

    * type classes

    * type inference

    You cannot type-check or normalize Annah expressions directly.  Instead,
    you `desugar` Annah expressions to Morte, and then type-check or normalize
    the Morte expressions using `M.typeOf` and `M.normalize`.

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
    , desugar

    ) where

import Annah.Parser
import Annah.Desugar
import Annah.Syntax

import qualified Morte.Core as M

{- $core
    The typical workflow is:

    * You parse a `Text` source using `exprFromText`

    * You `desugar` the Annah expression to Morte

    * You type-check the Morte expression using `M.typeOf`

    * You `M.normalize` the Morte expression
-}
