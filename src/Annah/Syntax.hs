{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | This module exports all the types used to build Annah's syntax tree

module Annah.Syntax (
    -- * Syntax
      M.Var(..)
    , M.Const(..)
    , Arg(..)
    , Let(..)
    , Data(..)
    , Type(..)
    , Family(..)
    , Bind(..)
    , Expr(..)
    ) where

import Data.String (IsString(..))
import Data.Text.Lazy (Text)
import qualified Morte.Core as M

{-| Argument for function or constructor definitions

> Arg "_" _A  ~       _A
> Arg  x  _A  ~  (x : _A)
-}
data Arg = Arg
    { argName :: Text
    , argType :: Expr
    }

{-|
> Let f [a1, a2] _A rhs  ~  let f a1 a2 : _A = rhs
-}
data Let = Let
    { letName :: Text
    , letArgs :: [Arg]
    , letType :: Expr
    , letRhs  :: Expr
    }

{-|
> Family [g1, g2] ts = given g1 g2 ts
-}
data Family = Family
    { familyGivens :: [Text]
    , familyTypes  :: [Type]
    }

{-|
> Type t f [d1, d2]  ~  type t d1 d2 fold f
-}
data Type = Type
    { typeName  :: Text
    , typeFold  :: Text
    , typeDatas :: [Data]
    }

{-|
> Data c [a1, a2]  ~  data c a1 a2
-}
data Data = Data
    { dataName :: Text
    , dataArgs :: [Arg]
    }

{-|
> Bind arg e  ~  arg <- e;
-}
data Bind = Bind
    { bindLhs :: Arg
    , bindRhs :: Expr
    }

-- | Syntax tree for expressions
data Expr
    -- | > Const c                         ~  c
    = Const M.Const
    -- | > Var (V x 0)                     ~  x
    --   > Var (V x n)                     ~  x@n
    | Var M.Var
    -- | > Lam x     _A  b                 ~  λ(x : _A) →  b
    | Lam Text Expr Expr
    -- | > Pi x      _A _B                 ~  ∀(x : _A) → _B
    | Pi  Text Expr Expr
    -- | > App f a                         ~  f a
    | App Expr Expr
    -- | > Annot a _A                      ~  a : _A
    | Annot Expr Expr
    -- | > Lets [l1, l2] e                 ~  l1 l2 in e
    | Lets [Let] Expr
    -- | > Family f e                      ~  f in e
    | Fam Family Expr
    -- | > Nat n                           ~  n
    | Natural Integer
    -- | > ASCII txt                       ~  txt
    | ASCII Text
    -- | > List t [x, y, z]                ~  [nil t,x,y,z]
    | List Expr [Expr]
    -- | > Path c [(o1, m1), (o2, m2)] o3  ~  [id c {o1} m1 {o2} m2 {o3}]
    | Path Expr [(Expr, Expr)] Expr
    -- | > Do m [b1, b2] b3                ~  do m { b1 b2 b3 }
    | Do Expr [Bind] Bind
    | Import M.Path

instance IsString Expr where
    fromString str = Var (fromString str)
