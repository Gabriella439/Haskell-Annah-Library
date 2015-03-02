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
    , Stmt(..)
    , Type(..)
    , Data(..)
    , Fold(..)
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
> Type f [Arg x _A, Arg y _B]  ~  type f (x : _A) (y : _B)
-}
data Type m = Type
    { typeName :: Text
    , typeArgs :: [Arg m]
    }

{-|
> Data f [Arg x _A, Arg y _B] _C  ~  data f (x : _A) (y : _B) : _C
-}
data Data m = Data
    { dataName :: Text
    , dataArgs :: [Arg m]
    , dataType :: Expr m
    }

{-|
> Fold f (Arg x _A)  ~  fold f (x : _A)
-}
data Fold m = Fold
    { foldName :: Text
    , foldArg  :: Arg m
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

{-| There are four types of statements:

    * @type@, which creates a new type constructor
    * @data@, which creates a new data constructor
    * @fold@, which creates a fold for a type
    * @let@ , which defines a function or value in terms of another expression

    Annah is liberal about statement order, but statements can only refer to
    values introduced by previous statements.  Also, statement order affects the
    derived implementation of types.  For example, if you define:

    > type Bool
    > data True  : Bool
    > data False : Bool
    > in   True

    ... then it will desugar to:

    > \(Bool : *) -> \(True : Bool) -> \(False : Bool) -> True

    ... but if you reorder the `True` and `False` constructors:

    > type Bool
    > data False : Bool
    > data True  : Bool
    > in   True

    ... then underlying implementation will change:

    > \(Bool : *) -> \(False : Bool) -> \(True : Bool) -> True

    This affects any generated `fold` for the type because the expected order
    of branches will correspond to the order of constructor statements.
-}
data Stmt m
    = StmtType (Type m)
    | StmtData (Data m)
    | StmtFold (Fold m)
    | StmtLet  (Let  m)

stmtName :: Stmt m -> Text
stmtName (StmtType t) = typeName t
stmtName (StmtData d) = dataName d
stmtName (StmtFold f) = foldName f
stmtName (StmtLet  l) =  letName l

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
    -- | > Stmts decls e     ~  decls in e
    | Stmts [Stmt m] (Expr m)
    -- | > Nat n             ~  n
    | Natural Integer
    | Import (m (Expr m))

instance IsString (Expr m) where
    fromString str = Var (fromString str)

-- | Evaluate all `Import`s, leaving behind a pure expression
loadExpr :: Expr IO -> IO (Expr m)
loadExpr (Const c      ) = return (Const c)
loadExpr (Var v        ) = return (Var v)
loadExpr (Lam x _A  b  ) = Lam x <$> loadExpr _A <*> loadExpr  b
loadExpr (Pi  x _A _B  ) = Pi  x <$> loadExpr _A <*> loadExpr _B
loadExpr (App f a      ) = App <$> loadExpr f <*> loadExpr a
loadExpr (Annot a _A   ) = Annot <$> loadExpr a <*> loadExpr _A
loadExpr (Stmts stmts e) = Stmts <$> mapM loadStmt stmts <*> loadExpr e
loadExpr (Natural n    ) = return (Natural n)
loadExpr (Import io    ) = io >>= loadExpr

loadStmt :: Stmt IO -> IO (Stmt m)
loadStmt (StmtType a) = StmtType <$> loadType a
loadStmt (StmtData a) = StmtData <$> loadData a
loadStmt (StmtFold a) = StmtFold <$> loadFold a
loadStmt (StmtLet  a) = StmtLet  <$> loadLet  a

loadType :: Type IO -> IO (Type m)
loadType (Type f args) = Type f <$> mapM loadArg args

loadData :: Data IO -> IO (Data m)
loadData (Data f args _B) = Data f <$> mapM loadArg args <*> loadExpr _B

loadFold :: Fold IO -> IO (Fold m)
loadFold (Fold f arg) = Fold f <$> loadArg arg

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
desugar (Annot a _A   ) = desugar (Stmts [StmtLet (Let "x" [] _A a)] "x")
desugar (Stmts stmts e) = desugarLets (desugarStmts stmts) e
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

{-| This is the meat of the Boehm-Berarducci encoding which translates the
    `type`, `data`, and `fold` declarations to their equivalent `let`
    expression.

    Annah permits data constructors to have duplicate names and Annah also
    permits data constructors to share the same name as type constructors.  This
    means that this is valid Annah code:

    > type A : *
    > data A : A
    > data A : A@1
    > in   A

    ... which compiles to:

    > \(A : *) -> \(A : A) -> \(A : A@1) -> A

    Constructor fields can also have duplicate field names, too.  One case where
    this is useful is when the user doesn't feel like naming fields and just
    gives every field the empty label, like this example:

    > type Pair (a : *) (b : *) : *
    > data MkPair (_ : a) (_ : b) : Pair a b
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
desugarStmts :: [Stmt Identity] -> [Let Identity]
desugarStmts stmts0 = result
  where
    universalArgs = do
        StmtType t <- stmts0
        typeArgs t

    result = do
    (stmtsBefore0, stmt0, stmtsAfter0) <- zippers stmts0

    {- Given a saturated type constructor, find:

        * the matching statement for that type constructor
        * the desugared let-binding for that type constructor
    -}
    let matchingDecl :: Expr Identity -> Maybe (Type Identity, Let Identity)
        matchingDecl e = do
            (M.V x0 n0, _) <- unapply e
            go x0 n0 (stmt0:stmtsBefore0) 0
          where
            go x n (stmt:stmts) k
                | stmtName stmt == x && n > 0 = go x (n - 1) stmts $! k + 1
                | stmtName stmt == x          = do
                    StmtType t <- return stmt
                    l <- safeIndex (length stmtsBefore0 - k) result
                    return (t, l)
                | otherwise                   = go x  n      stmts $! k + 1
            go _ _  []          _             = Nothing

    -- Compute the DeBruijn indices for constructors in case of duplicate names
    let con  = stmtName stmt0 `isShadowedBy` conNames stmtsAfter0
    let cons = do
            (_, conName, conNamesAfter) <- zippers (conNames stmts0)
            return (Var (conName `isShadowedBy` conNamesAfter))

    let makeRhs piOrLam args = go stmts0
          where
            go (StmtType t:stmts) =
                piOrLam (typeName t) (pi (typeArgs t) (Const M.Star)) (go stmts)
            go (StmtData d:stmts) =
                piOrLam (dataName d) (pi (dataArgs d) (dataType d  )) (go stmts)
            go (_:stmts) = go stmts
            go  []       = apply con conArgs

            conArgs = do
                (_, arg, argsAfter) <- zippers args
                let names1 = map argName argsAfter
                let names2 = conNames stmts0
                let v      = argName arg `isShadowedBy` (names1 ++ names2)
                return (case matchingDecl (argType arg) of
                    Nothing -> Var v
                    _       -> apply v cons )

    return (case stmt0 of
        StmtType t0 -> Let (typeName t0) (typeArgs t0) (Const M.Star) rhs
          where
            rhs = makeRhs Pi (typeArgs t0)

        StmtData d0 -> Let (dataName d0) universalArgs  abstractType  rhs'
          where
            abstractType = pi (dataArgs d0) (dataType d0)

            dataArgs' = do
                Arg x _A <- dataArgs d0
                let m = do
                        (_, l) <- matchingDecl _A
                        return (letRhs l)
                let _A' = case m of
                        Just _A' -> _A'
                        Nothing  -> _A
                return (Arg x _A')

            rhs' = lam dataArgs' (makeRhs Lam (dataArgs d0))

        StmtFold f0 -> case matchingDecl _A of
            Just (_, l) -> Let (foldName f0) universalArgs foldType' rhs
              where
                foldType' = Pi x _A (letRhs l)
                rhs = Lam x (letRhs l) (Var (M.V x 0))
          where
            Arg x _A = foldArg f0
            -- TODO: Better error handling

        StmtLet  l0 -> l0 )

-- | Returns `True` if the given `StmtType` is a type or data constructor
isCons :: Stmt m -> Bool
isCons (StmtType _) = True
isCons (StmtData _) = True
isCons  _           = False

-- | The names of all type or data constructors
conNames :: [Stmt m] -> [Text]
conNames = map stmtName . filter isCons

-- | Unapply a function, returning the function name and the arguments
unapply :: Expr m -> Maybe (M.Var, [Expr m])
unapply e0 = do
    ~(f, diffAs) <- go e0
    return (f, diffAs [])
  where
    go (App e a) = do
        ~(f, diffAs) <- go e
        return (f, diffAs . (a:))
    go (Var v  ) = Just (v, id)
    go  _        = Nothing

-- | Apply a function to a list of arguments
apply :: M.Var -> [Expr m] -> Expr m
apply f as = foldr (flip App) (Var f) (reverse as)

-- | Index safely into a list
safeIndex :: Int -> [a] -> Maybe a
safeIndex _  []    = Nothing
safeIndex 0 (a:_ ) = Just a
safeIndex n (_:as) = n' `seq` safeIndex n' as
  where
    n' = n - 1

{-| Compute the correct DeBruijn index for a synthetic `Var` (`x`) by providing
    all variables bound in between when `x` is introduced and when `x` is used.
-}
isShadowedBy :: Text -> [Text] -> M.Var
x `isShadowedBy` vars = M.V x (length (filter (== x) vars))

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

buildStmt :: Stmt Identity -> Builder
buildStmt (StmtType t) = buildType t
buildStmt (StmtData d) = buildData d
buildStmt (StmtFold f) = buildFold f
buildStmt (StmtLet  l) = buildLet  l

buildType :: Type Identity -> Builder
buildType (Type n args)
    =   "type "
    <>  fromLazyText n
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)

buildData :: Data Identity -> Builder
buildData (Data n args t)
    =   "data "
    <>  fromLazyText n
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)
    <>  ": "
    <>  buildExpr t
    <>  " "

buildFold :: Fold Identity -> Builder
buildFold (Fold n arg)
    =   "fold "
    <>  fromLazyText n
    <>  " "
    <>  buildArg arg
    <>  " "

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
        Stmts ls e'    -> quoteAbove 1 (
            mconcat (map buildStmt ls) <> "in " <> go 1 e' )
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
