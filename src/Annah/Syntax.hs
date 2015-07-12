{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

-- | This module exports all the types used to build Annah's syntax tree

module Annah.Syntax (
    -- * Syntax
      M.Var(..)
    , M.Const(..)
    , Arg(..)
    , ProductTypeField(..)
    , ProductValueField(..)
    , Let(..)
    , Data(..)
    , Type(..)
    , Family(..)
    , Bind(..)
    , Expr(..)
    ) where

import Data.Monoid (mconcat, (<>))
import Data.String (IsString(..))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (Builder)
import qualified Morte.Core as M

{-| Argument for function or constructor definitions

> Arg "_" _A  ~       _A
> Arg  x  _A  ~  (x : _A)
-}
data Arg m = Arg
    { argName :: Text
    , argType :: Expr m
    }

instance Buildable a => Buildable (Arg a) where
    build (Arg "_" _A) =                            build _A
    build (Arg  x  _A) = "(" <> build x <> " : " <> build _A <> ")"

{-| Field of a product type

> ProductTypeField  x  _A  ~  x : _A
> ProductTypeField "_" _A  ~      _A
-}
data ProductTypeField m = ProductTypeField
    { productTypeName :: Text
    , productTypeType :: Expr m
    }

instance Buildable a => Buildable (ProductTypeField a) where
    build (ProductTypeField x _A) =
        if x == "_"
        then build _A
        else build x <> " : " <> build _A

{-| Field of a product value

> ProductValueField a _A  ~  a : _A
-}
data ProductValueField m = ProductValueField
    { productValueFieldExpr :: Expr m
    , productValueFieldType :: Expr m
    }

instance Buildable a => Buildable (ProductValueField a) where
    build (ProductValueField a b) = build a <> " : " <> build b

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

instance Buildable a => Buildable (Family a) where
    build (Family [] ts) = mconcat (map build ts)
    build (Family gs ts)
        =   "given "
        <>  mconcat (map (\g -> build g <> " ") gs)
        <>  mconcat (map build ts)

{-|
> Type t f [d1, d2]  ~  type t d1 d2 fold f
-}
data Type m = Type
    { typeName  :: Text
    , typeFold  :: Text
    , typeDatas :: [Data m]
    }

instance Buildable a => Buildable (Type a) where
    build (Type t f ds)
        =   "type "
        <>  build t
        <>  mconcat (map build ds)
        <>  (if f == "_" then "" else " fold " <> build f <> " ")

{-|
> Data c [a1, a2]  ~  data c a1 a2
-}
data Data m = Data
    { dataName :: Text
    , dataArgs :: [Arg m]
    }

instance Buildable a => Buildable (Data a) where
    build (Data d args)
        =   "data "
        <>  build d
        <>  " "
        <>  mconcat (map (\arg -> build arg <> " ") args)

{-|
> Bind arg e  ~  arg <- e;
-}
data Bind m = Bind
    { bindLhs :: Arg m
    , bindRhs :: Expr m
    }

instance Buildable a => Buildable (Bind a) where
    build (Bind (Arg x _A) e) =
        build x <> " : " <> build _A <> " <- " <> build e <> "; "

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
    -- | > ProductValue [f1, f2]           ~  <1,f1,f2>
    | ProductValue [ProductValueField m]
    -- | > ProductType [f1, f2]            ~  {1,f1,f2}
    | ProductType [ProductTypeField m]
    -- | > SumConstructor i j              ~  iofj
    | SumConstructor Int Int
    -- | > SumType [t1, t2]                ~  {0|t1|t2}
    | SumType [Expr m]
    -- | > List t [x, y, z]                ~  [nil t,x,y,z]
    | List (Expr m) [Expr m]
    -- | > ListType t                      ~  [t]
    | ListType (Expr m)
    -- | > Path c [(o1, m1), (o2, m2)] o3  ~  [id c (|o1|) m1 (|o2|) m2 (|o3|)]
    | Path (Expr m) [(Expr m, Expr m)] (Expr m)
    -- | > Do m [b1, b2] b3                ~  do m { b1 b2 b3 }
    | Do (Expr m) [Bind m] (Bind m)
    | Import m

instance IsString (Expr m) where
    fromString str = Var (fromString str)

instance Buildable a => Buildable (Expr a) where
    build = go 0
      where
        go :: Buildable a => Int -> Expr a -> Builder
        go prec e = case e of
            Const c             -> build c
            Var x               -> build x
            Lam x _A b          -> quoteAbove 1 (
                    "λ"
                <>  "(" <> build x <> " : " <>  go 1 _A <>  ")"
                <>  " → "
                <>  go 1 b )
            Pi  x _A b          -> quoteAbove 1 (
                    (if x /= "_"
                     then "∀(" <> build x <> " : " <> go 1 _A <> ")"
                     else go 2 _A )
                <>  " → "
                <>  go 1 b )
            App f a             -> quoteAbove 2 (go 2 f <> " " <> go 3 a)
            Annot s t           -> quoteAbove 0 (go 2 s <> " : " <> go 1 t)
            Lets ls e'          -> quoteAbove 1 (
                mconcat (map build ls) <> "in " <> go 1 e' )
            Fam f e'            -> quoteAbove 1 (build f <> "in " <> go 1 e')
            Natural n           -> build n
            ASCII   txt         -> "\"" <> build txt <> "\""
            SumConstructor m n  -> build m <> "to" <> build n
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
                    "[nil " <> build t
                <> mconcat (map (\a -> "," <> build a) as)
                <>  "]"
            ListType t          -> "[" <> build t <> "]"
            Path c oms o0       ->
                    "[id " <> build c
                <> mconcat
                    (map (\(o, m) -> " (|" <> build o <> "|) " <> build m) oms)
                <> " (|" <> build o0 <> "|)]"
            Do m bs b           ->
                    "do " <> build m <> " { "
                <>  mconcat (map build bs)
                <>  build b
                <>  "}"
            Import p            -> build p
          where
            quoteAbove :: Int -> Builder -> Builder
            quoteAbove n b = if prec > n then "(" <> b <> ")" else b

instance Buildable a => Buildable (Let a) where
    build (Let n args t r)
        =   "let "
        <>  build n
        <>  " "
        <>  mconcat (map (\arg -> build arg <> " ") args)
        <>  ": "
        <>  build t
        <>  " = "
        <>  build r
        <>  " "
