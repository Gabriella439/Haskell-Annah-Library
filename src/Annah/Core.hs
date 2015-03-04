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

import Control.Applicative (pure, empty, (<$>), (<*>))
import Data.Functor.Identity (Identity, runIdentity)
import Data.Monoid (Monoid(..), (<>))
import Data.String (IsString(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder.Int (decimal)
import Data.Text.Lazy.Builder (Builder, toLazyText, fromLazyText)
import qualified Morte.Core as M
import Prelude hiding (const, pi)

{-| Argument for function or constructor definitions

> Arg x _A  ~  (x : _A)
-}
data Arg m = Arg
    { argName :: Text
    , argType :: Expr m
    }

{-|
> Let f [Arg x _A, Arg y _B] _C rhs  ~  let f (x : _A) (y : _B) : _C = rhs
-}
data Let m = Let
    { letName :: Text
    , letArgs :: [Arg m]
    , letType :: Expr m
    , letRhs  :: Expr m
    }

data Family m = Family
    { familyGivens :: [Text]
    , familyTypes  :: [Type m]
    }

data Type m = Type
    { typeName  :: Text
    , typeDatas :: [Data m]
    }

data Data m = Data
    { dataName :: Text
    , dataArgs :: [Arg m]
    }

{-| Syntax tree for expressions

    Note that equality of @annah@ expressions is purely syntactic
-}
data Expr m
    -- | > Const c           ~  c
    = Const M.Const
    -- | > Var (V x 0)       ~  x
    --   > Var (V x 0)       ~  x
    | Var M.Var
    -- | > Lam x     _A  b   ~  λ(x : _A) →  b
    | Lam Text (Expr m) (Expr m)
    -- | > Pi x      _A _B   ~  ∀(x : _A) → _B
    --   > Pi unused _A _B   ~        _A  → _B
    | Pi  Text (Expr m) (Expr m)
    -- | > App f a           ~  f a
    | App (Expr m) (Expr m)
    -- | > Annot a _A        ~  a : _A
    | Annot (Expr m) (Expr m)
    | Lets [Let m] (Expr m)
    | Fam (Family m) (Expr m)
    -- | > Nat n             ~  n
    | Natural Integer
    | Import (m (Expr m))

instance IsString (Expr m) where
    fromString str = Var (fromString str)

-- | Evaluate all `Import`s, leaving behind a pure expression
loadExpr :: Expr IO -> IO (Expr m)
loadExpr (Const c      ) = pure (Const c)
loadExpr (Var v        ) = pure (Var v)
loadExpr (Lam x _A  b  ) = Lam x <$> loadExpr _A <*> loadExpr  b
loadExpr (Pi  x _A _B  ) = Pi  x <$> loadExpr _A <*> loadExpr _B
loadExpr (App f a      ) = App <$> loadExpr f <*> loadExpr a
loadExpr (Annot a _A   ) = Annot <$> loadExpr a <*> loadExpr _A
loadExpr (Lets ls e    ) = Lets <$> mapM loadLet ls <*> loadExpr e
loadExpr (Fam f e      ) = Fam <$> loadFamily f <*> loadExpr e
loadExpr (Natural n    ) = pure (Natural n)
loadExpr (Import io    ) = io >>= loadExpr

loadFamily :: Family IO -> IO (Family m)
loadFamily (Family as bs) = Family as <$> mapM loadType bs

loadType :: Type IO -> IO (Type m)
loadType (Type a bs) = Type a <$> mapM loadData bs

loadData :: Data IO -> IO (Data m)
loadData (Data a bs) = Data a <$> mapM loadArg bs

loadLet :: Let IO -> IO (Let m)
loadLet (Let f args _B b) =
    Let f <$> mapM loadArg args <*> loadExpr _B <*> loadExpr b

loadArg :: Arg IO -> IO (Arg m)
loadArg (Arg x _A) = Arg x <$> loadExpr _A

{-| Convert an Annah expression to a Morte expression

> resugar . desugar = id  -- But not the other way around!
-}
desugar :: Expr Identity -> M.Expr
desugar (Const c      ) = M.Const c
desugar (Var v        ) = M.Var   v
desugar (Lam x _A  b  ) = M.Lam x (desugar _A) (desugar  b)
desugar (Pi  x _A _B  ) = M.Pi  x (desugar _A) (desugar _B)
desugar (App f a      ) = M.App (desugar f) (desugar a)
desugar (Annot a _A   ) = desugar (Lets [Let "x" [] _A a] "x")
desugar (Lets ls e    ) = desugarLets  ls               e
desugar (Fam f e      ) = desugarLets (desugarFamily f) e
desugar (Natural n    ) = desugarNat n
desugar (Import m     ) = desugar (runIdentity m)

desugarNat :: Integer -> M.Expr
desugarNat n0 =
    M.Lam "Nat" (M.Const M.Star) (
        M.Lam "Zero" "Nat" (
            M.Lam "Succ" (M.Pi "pred" "Nat" "Nat") (go n0) ) )
  where
    go n | n <= 0    = "Zero"
         | otherwise = M.App "Succ" (go $! n - 1)

resugarNat :: M.Expr -> Maybe Integer
resugarNat (
    M.Lam "Nat" (M.Const M.Star) (
        M.Lam "Zero" (M.Var (M.V "Nat" 0)) (
            M.Lam "Succ"
                  (M.Pi _ (M.Var (M.V "Nat" 0)) (M.Var (M.V "Nat" 0))) e0) ))
    = go e0 0
  where
    go (M.Var (M.V "Zero" 0))           n = pure n
    go (M.App (M.Var (M.V "Succ" 0)) e) n = go e $! n + 1
    go  _                               _ = empty
resugarNat _ = empty

-- | A type or data constructor
data Cons = Cons
    { consName :: Text
    , consArgs :: [Arg Identity]
    , consType :: Expr Identity
    }

{-| This is the meat of the Boehm-Berarducci encoding which translates type
    declarations into their equivalent `let` expressions.

    Annah permits data constructors to have duplicate names and Annah also
    permits data constructors to share the same name as type constructors.  This
    means that this is valid Annah code:

    > type A
    > data A
    > data A
    > in   A

    ... which compiles to:

    > \(A : *) -> \(A : A) -> \(A : A@1) -> A

    Constructor fields can also have duplicate field names, too.  One case where
    this is useful is when the user doesn't feel like naming fields and just
    gives every field the empty label, like this example:

    > given a b
    > type Pair
    > data MkPair (_ : a) (_ : b)
    > in   MkPair

    ... which compiles to:

    >     \(a : *)
    > ->  \(b : *)
    > ->  \(_ : a)
    > ->  \(_ : b)
    > ->  \(Pair : *)
    > ->  \(MkPair : a -> b -> Pair)
    > ->  MkPair _@1 _
-}
desugarFamily :: Family Identity -> [Let Identity]
desugarFamily fam = typeLets ++ dataLets
    -- TODO: Add folds?
  where
    universalArgs :: [Arg Identity]
    universalArgs = do
        given <- familyGivens fam
        return (Arg given (Const M.Star))

    universalVars :: [Expr Identity]
    universalVars = do
        given <- familyGivens fam
        return (Var (M.V given 0))

    typeConstructors :: [Cons]
    typeConstructors = do
        t <- familyTypes fam
        return (Cons (typeName t) [] (Const M.Star))

    dataConstructors :: [Cons]
    dataConstructors = do
        (_       , t, tsAfter) <- zippers (familyTypes fam)
        (dsBefore, d, _      ) <- zippers (typeDatas t)
        let names1 = map typeName tsAfter
        let names2 = map dataName dsBefore
        let typeVar  = typeName t `isShadowedBy` (names1 ++ names2)
        return (Cons (dataName d) (dataArgs d) typeVar)

    constructors :: [Cons]
    constructors = typeConstructors ++ dataConstructors

    makeRhs piOrLam con = go constructors
      where
        go ((Cons x args _A):stmts) = piOrLam x (pi args _A) (go stmts)
        go  []                      = con

    typeLets :: [Let Identity]
    typeLets = do
        (_, t, typeConstructorsAfter) <- zippers typeConstructors
        let names1   = map consName typeConstructorsAfter
        let names2   = map consName dataConstructors
        let con      = consName t `isShadowedBy` (names1 ++ names2)
        let letRhs'  = makeRhs Pi con
        return (Let (consName t) universalArgs (consType t) letRhs')

    -- TODO: Enforce that argument types are `Var`s?
    desugarType :: Expr Identity -> Maybe (Expr Identity)
    desugarType (Var (M.V x0 n0)) = go0 dataConstructors x0 n0
      where
        go0 (d:ds) x n | consName d == x =
            if n > 0 then go0 ds x $! n - 1 else empty
                       | otherwise       = go0 ds x n
        go0  []    x n                   = go1 typeLets x n

        go1 (t:ts) x n | letName  t == x =
            if n > 0 then go1 ts x $! n - 1 else pure (letRhs t)
                       | otherwise       = go1 ts x n
        go1  []    _ _                   = empty
    desugarType  _        = empty

    consVars :: [Expr Identity]
    consVars = do
        (_, name, namesAfter) <- zippers (map consName constructors)
        return (name `isShadowedBy` namesAfter)

    dataLets :: [Let Identity]
    dataLets = do
        (_, d, dsAfter) <- zippers dataConstructors
        let conVar  = consName d `isShadowedBy` map consName dsAfter
        let conArgs = do
                (_, arg, argsAfter) <- zippers (consArgs d)
                let names1 = map argName  argsAfter
                let names2 = map consName constructors
                let argVar = argName arg `isShadowedBy` (names1 ++ names2)
                return (case desugarType (argType arg) of
                    Nothing ->       argVar
                    _       -> apply argVar consVars )
        let (lhsArgs, rhsArgs) = unzip (do
                Arg x _A <- consArgs d
                return (case desugarType _A of
                        Just _A' -> (Arg x (apply _A universalVars), Arg x _A')
                        Nothing  -> (Arg x        _A               , Arg x _A ) ) )
        let letType' = pi  lhsArgs (apply (consType d) universalVars)
        let letRhs'  = lam rhsArgs (makeRhs Lam (apply conVar conArgs))
        return (Let (consName d) universalArgs letType' letRhs')

-- | Apply an expression to a list of arguments
apply :: Expr m -> [Expr m] -> Expr m
apply f as = foldr (flip App) f (reverse as)

{-| Compute the correct DeBruijn index for a synthetic `Var` (`x`) by providing
    all variables bound in between when `x` is introduced and when `x` is used.
-}
isShadowedBy :: Text -> [Text] -> Expr m
x `isShadowedBy` vars = Var (M.V x (length (filter (== x) vars)))

pi :: [Arg m] -> Expr m -> Expr m
pi args e = foldr (\(Arg x _A) -> Pi x _A) e args

lam :: [Arg m] -> Expr m -> Expr m
lam args e = foldr (\(Arg x _A) -> Lam x _A) e args

{-| `desugarLets` converts this:

> let f0 (x00 : _A00) ... (x0j : _A0j) _B0 = b0
> ..
> let fi (xi0 : _Ai0) ... (xij : _Aij) _Bi = bi
> in  e

... into this:

> (   \(f0 : forall (x00 : _A00) -> ... -> forall (x0j : _A0j) -> _B0)
> ->  ...
> ->  \(fi : forall (xi0 : _Ai0) -> ... -> forall (xij : _Aij) -> _Bi)
> ->  e
> )
>
> (\(x00 : _A00) -> ... -> \(x0j : _A0j) -> b0)
> ...
> (\(xi0 : _Ai0) -> ... -> \(xij : _Aij) -> bi)

-}
desugarLets :: [Let Identity] -> Expr Identity -> M.Expr
desugarLets lets e = apps
  where
    -- > (   \(f0 : forall (x00 : _A00) -> ... -> forall (x0j : _A0j) -> _B0)
    -- > ->  ...
    -- > ->  \(fi : forall (xi0 : _Ai0) -> ... -> forall (xij : _Aij) -> _Bi)
    -- > ->  e
    -- > )
    lams = foldr
        (\(Let fn args _Bn _) rest ->
            -- > forall (xn0 : _An0) -> ... -> forall (xnj : _Anj) -> _Bn
            let rhsType = pi args _Bn

            -- > \(fn : rhsType) -> rest
            in  M.Lam fn (desugar rhsType) rest )
        (desugar e)
        lets

    -- > lams
    -- > (\(x00 : _A00) -> ... -> \(x0j : _A0j) -> b0)
    -- > ...
    -- > (\(xi0 : _Ai0) -> ... -> \(xij : _Aij) -> bi)
    apps = foldr
        (\(Let _ args _ bn) rest ->
            -- > rest (\(xn0 : _An0) -> ... -> \(xnj : _Anj) -> bn)
            M.App rest (desugar (lam args bn)) )
        lams
        (reverse lets)

-- | > zippers [1, 2, 3] = [([], 1, [2, 3]), ([1], 2, [3]), ([2, 1], 3, [])]
zippers :: [a] -> [([a], a, [a])]
zippers  []           = []
zippers (stmt:stmts') = z:go z
  where
    z = ([], stmt, stmts')

    go ( _, _, []  ) = []
    go (ls, m, r:rs) = z':go z'
      where
        z' = (m:ls, r, rs)

-- | Convert a Morte expression to an Annah expression
resugar :: M.Expr -> Expr m
resugar   (M.Const c    ) = Const c
resugar   (M.Var v      ) = Var v
resugar e@(M.Lam x _A  b) = case resugarNat e of
    Nothing -> Lam x (resugar _A) (resugar  b)
    Just n  -> Natural n
resugar   (M.Pi  x _A _B) = Pi  x (resugar _A) (resugar _B)
resugar   (M.App f0 a0  ) = App (resugar f0) (resugar a0)

buildArg :: Arg Identity -> Builder
buildArg (Arg x _A) = "(" <> fromLazyText x <> " : " <> buildExpr _A <> ")"

buildFamily :: Family Identity -> Builder
buildFamily (Family gs ts)
    =   "given "
    <>  mconcat (map (\g -> fromLazyText g <> " ") gs)
    <>  mconcat (map buildType ts)

buildType :: Type Identity -> Builder
buildType (Type t ds)
    =   "type "
    <>  fromLazyText t
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
        Const c        -> M.buildConst c
        Var x          -> M.buildVar x
        Lam x _A b     -> quoteAbove 1 (
                "λ("
            <>  fromLazyText x
            <>  " : "
            <>  go 1 _A
            <>  ") → "
            <>  go 1 b )
        Pi  x _A b    -> quoteAbove 1 (
                (if M.used x (desugar b)
                 then "∀(" <> fromLazyText x <> " : " <> go 1 _A <> ")"
                 else go 2 _A )
            <>  " → "
            <>  go 1 b )
        App f a        -> quoteAbove 2 (go 2 f <> " " <> go 3 a)
        Annot s t      -> quoteAbove 0 (go 2 s <> " : " <> go 1 t)
        Lets ls e'     -> quoteAbove 1 (
            mconcat (map buildLet ls) <> "in " <> go 1 e' )
        Fam f e'       -> quoteAbove 1 (buildFamily f <> "in " <> go 1 e')
        Natural n      -> decimal n
        Import m       -> go prec (runIdentity m)
      where
        quoteAbove :: Int -> Builder -> Builder
        quoteAbove n b = if prec > n then "(" <> b <> ")" else b

{-| Pretty-print an expression

    The result is a syntactically valid Annah program
-}
prettyExpr :: Expr Identity -> Text
prettyExpr = toLazyText . buildExpr
