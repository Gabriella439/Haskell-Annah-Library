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
data Arg m = Arg
    { argName :: Text
    , argType :: Expr m
    }

{-|
> Let f [a1, a2] _A rhs  ~  let f a1 a2 : _A = rhs
-}
data Let m = Let
    { letName :: Text
    , letArgs :: [Arg m]
    , letType :: Expr m
    , letRhs  :: Expr m
    }

{-|
> Family [g1, g2] ts = given g1 g2 ts
-}
data Family m = Family
    { familyGivens :: [Arg m]
    , familyTypes  :: [Type m]
    }

{-|
> Type t f [d1, d2]  ~  type t d1 d2 fold f
-}
data Type m = Type
    { typeName  :: Text
    , typeFold  :: Text
    , typeDatas :: [Data m]
    }

{-|
> Data c [a1, a2]  ~  data c a1 a2
-}
data Data m = Data
    { dataName :: Text
    , dataArgs :: [Arg m]
    }

{-|
> Bind arg e  ~  arg <- e;
-}
data Bind m = Bind
    { bindLhs :: Arg m
    , bindRhs :: Expr m
    }

-- | Syntax tree for expressions
data Expr m
    -- | > Const c                         ~  c
    = Const M.Const
    -- | > Var (V x 0)                     ~  x
    --   > Var (V x n)                     ~  x@n
    | Var M.Var
    -- | > Lam x     _A  b                 ~  λ(x : _A) →  b
    | Lam Text (Expr m) (Expr m)
    -- | > Pi x      _A _B                 ~  ∀(x : _A) → _B
    | Pi  Text (Expr m) (Expr m)
    -- | > App f a                         ~  f a
    | App (Expr m) (Expr m)
    -- | > Annot a _A                      ~  a : _A
    | Annot (Expr m) (Expr m)
    -- | > Lets [l1, l2] e                 ~  l1 l2 in e
    | Lets [Let m] (Expr m)
    -- | > Family f e                      ~  f in e
    | Fam (Family m) (Expr m)
    -- | > Nat n                           ~  n
    | Natural Integer
    -- | > ASCII txt                       ~  txt
    | ASCII Text
    -- | > List t [x, y, z]                ~  [nil t,x,y,z]
    | List (Expr m) [Expr m]
    -- | > Path c [(o1, m1), (o2, m2)] o3  ~  [id c (|o1|) m1 (|o2|) m2 (|o3|)]
    | Path (Expr m) [(Expr m, Expr m)] (Expr m)
    -- | > Do m [b1, b2] b3                ~  do m { b1 b2 b3 }
    | Do (Expr m) [Bind m] (Bind m)
    | Import m

instance IsString (Expr m) where
    fromString str = Var (fromString str)
