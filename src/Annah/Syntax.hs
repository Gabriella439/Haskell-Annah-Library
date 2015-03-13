-- | This module exports all the types used to build Annah's syntax tree

module Annah.Syntax (
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
    ) where

import Data.String (IsString(..))
import Data.Text.Lazy (Text)
import qualified Morte.Core as M

{-| Argument for function or constructor definitions

> Arg x _A  ~  (x : _A)
-}
data Arg m = Arg
    { argName :: Text
    , argType :: Expr m
    }

{-| Field of a product type

> ProductTypeField x _A  ~  x : _A
-}
data ProductTypeField m = ProductTypeField
    { productTypeName :: Text
    , productTypeType :: Expr m
    }

{-| Field of a product value

> ProductValueField a _A  ~  a : _A
-}
data ProductValueField m = ProductValueField
    { productValueFieldExpr :: Expr m
    , productValueFieldType :: Expr m
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
    { familyGivens :: [Text]
    , familyTypes  :: [Type m]
    }

{-|
> Type t f [d1, d2]  ~  type t fold f d1 d2
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

-- | Syntax tree for expressions
data Expr m
    -- | > Const c                ~  c
    = Const M.Const
    -- | > Var (V x 0)            ~  x
    --   > Var (V x 0)            ~  x
    | Var M.Var
    -- | > Lam x     _A  b        ~  λ(x : _A) →  b
    | Lam Text (Expr m) (Expr m)
    -- | > Pi x      _A _B        ~  ∀(x : _A) → _B
    --   > Pi unused _A _B        ~        _A  → _B
    | Pi  Text (Expr m) (Expr m)
    -- | > App f a                ~  f a
    | App (Expr m) (Expr m)
    -- | > Annot a _A             ~  a : _A
    | Annot (Expr m) (Expr m)
    -- | > Lets [l1, l2] e        ~ l1 l2 in e
    | Lets [Let m] (Expr m)
    | Fam (Family m) (Expr m)
    -- | > Nat n                  ~  n
    | Natural Integer
    -- | > ProductValue [f1, f2]  ~  (f1, f2)
    | ProductValue [ProductValueField m]
    -- | > ProductType [f1, f2]   ~  {f1, f2}
    | ProductType [ProductTypeField m]
    -- | > ProductAccessor 1 2    ~  1of2
    | ProductAccessor Int Int
    | Import (m (Expr m))

instance IsString (Expr m) where
    fromString str = Var (fromString str)
