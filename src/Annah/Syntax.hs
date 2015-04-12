-- | This module exports all the types used to build Annah's syntax tree

module Annah.Syntax (
    -- * Syntax
      M.Var(..)
    , M.Const(..)
    , Arg(..)
    , ProductTypeField(..)
    , ProductTypeSectionField(..)
    , ProductValueField(..)
    , ProductValueSectionField(..)
    , SumTypeSectionField(..)
    , ListTypeSectionField(..)
    , Let(..)
    , Data(..)
    , Type(..)
    , Family(..)
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

-- | Field of a product type section
data ProductTypeSectionField m
    = EmptyTypeField
    | TypeField (ProductTypeField m)

{-| Field of a product value

> ProductValueField a _A  ~  a : _A
-}
data ProductValueField m = ProductValueField
    { productValueFieldExpr :: Expr m
    , productValueFieldType :: Expr m
    }

-- | Field of a product value section
data ProductValueSectionField m
    = EmptyValueField
    | TypeValueField (Expr m)
    | ValueField (ProductValueField m)

-- | Field of a sum type section
data SumTypeSectionField m
    = EmptySumTypeField
    | SumTypeField (Expr m)

-- | Field of a list type section
data ListTypeSectionField m
    = EmptyListTypeSectionField
    | ListTypeSectionField (Expr m)

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
    -- | > Const c                         ~  c
    = Const M.Const
    -- | > Var (V x 0)                     ~  x
    --   > Var (V x 0)                     ~  x
    | Var M.Var
    -- | > Lam x     _A  b                 ~  λ(x : _A) →  b
    | Lam Text (Expr m) (Expr m)
    -- | > Pi x      _A _B                 ~  ∀(x : _A) → _B
    --   > Pi unused _A _B                 ~        _A  → _B
    | Pi  Text (Expr m) (Expr m)
    -- | > App f a                         ~  f a
    | App (Expr m) (Expr m)
    -- | > Annot a _A                      ~  a : _A
    | Annot (Expr m) (Expr m)
    -- | > Lets [l1, l2] e                 ~  l1 l2 in e
    | Lets [Let m] (Expr m)
    | Fam (Family m) (Expr m)
    -- | > Nat n                           ~  n
    | Natural Integer
    -- | > ASCII str                       ~  str
    | ASCII Text
    -- | > ProductValue [f1, f2]           ~  <1,f1,f2>
    | ProductValue [ProductValueSectionField m]
    -- | > ProductType [f1, f2]            ~  {1,f1,f2}
    | ProductType [ProductTypeSectionField m]
    -- | > SumConstructor i j              ~  itoj
    | SumConstructor Int Int
    -- | > SumType [t1, t2]                ~  {0|t1|t2}
    | SumType [SumTypeSectionField m]
    -- | > List t [x, y, z]                ~  [* t,x,y,z]
    | List (Expr m) [Expr m]
    -- | > ListType t                      ~  [t]
    | ListType (ListTypeSectionField m)
    -- | > Path c [(o1, m1), (o2, m2)] o3  ~  [. c (|o1|) m1 (|o2|) m2 (|o3|)]
    | Path (Expr m) [(Expr m, Expr m)] (Expr m)
    | Import m

instance IsString (Expr m) where
    fromString str = Var (fromString str)
