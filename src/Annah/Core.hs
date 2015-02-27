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
    , Decl(..)
    , Stmt(..)
    , StmtType(..)
    , Expr(..)

    -- * Core functions
    , load
    , desugar
    , resugar

    -- * Utilities
    , prettyExpr
    , buildExpr
    ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad (guard)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Monoid (Monoid(..), (<>))
import Data.String (IsString(..))
import Data.Text.Lazy (Text)
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

{-| Declaration for function or constructor definitions

> Decl f [Arg x _A, Arg y _B] _C  ~  f (x : _A) (y : _B) : _C
-}
data Decl m = Decl
    { declName :: Text
    , declArgs :: [Arg m]
    }

{-| There are four types of statements:

* @type@, which creates a new type constructor
* @data@, which creates a new data constructor
* @fold@, which creates a fold for a type
* @let@, which defines a function or value in terms of another expression

    Only @let@ statements have a right-hand side
-}
data StmtType m
    = Type
    | Data (Expr m)
    | Fold
    | Let (Expr m) (Expr m)

{-| A @type@ \/ @data@ \/ @let@ declaration

> Stmt (Decl f [Arg x _A, Arg y _B] _C)  Type    ~  type f (x : _A) (y : _B) : _C
> Stmt (Decl f [Arg x _A, Arg y _B] _C)  Data    ~  data f (x : _A) (y : _B) : _C
> Stmt (Decl f [Arg x _A, Arg y _B] _C) (Let z)  ~  let  f (x : _A) (y : _B) : _C = z
-}
data Stmt m = Stmt
    { stmtDecl :: Decl m
    , stmtType :: StmtType m
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
    -- | > Stmts decls e     ~  decls in e
    | Stmts [Stmt m] (Expr m)
    | Import (m (Expr m))

instance IsString (Expr m) where
    fromString str = Var (fromString str)

load :: Expr IO -> IO (Expr m)
load (Const c      ) = return (Const c)
load (Var v        ) = return (Var v)
load (Lam x _A  b  ) = Lam x <$> load _A <*> load  b
load (Pi  x _A _B  ) = Pi  x <$> load _A <*> load _B
load (App f a      ) = App <$> load f <*> load a
load (Annot a _A   ) = Annot <$> load a <*> load _A
load (Stmts stmts e) = Stmts <$> mapM loadStmt stmts <*> load e
load (Import io    ) = io >>= load

loadStmt :: Stmt IO -> IO (Stmt m)
loadStmt (Stmt d st) = Stmt <$> loadDecl d <*> loadStmtType st

loadDecl :: Decl IO -> IO (Decl m)
loadDecl (Decl x args) = Decl x <$> mapM loadArg args

loadStmtType :: StmtType IO -> IO (StmtType m)
loadStmtType  Type     = return Type
loadStmtType (Data a ) = Data <$> load a
loadStmtType  Fold     = return Fold
loadStmtType (Let a b) = Let <$> load a <*> load b

loadArg :: Arg IO -> IO (Arg m)
loadArg (Arg x _A) = Arg x <$> load _A

{-| Convert an Annah expression to a Morte expression

> resugar . desugar = id  -- But not the other way around!
-}
desugar :: Expr Identity -> M.Expr
desugar (Const c      ) = M.Const c
desugar (Var v        ) = M.Var   v
desugar (Lam x _A  b  ) = M.Lam x (desugar _A) (desugar  b)
desugar (Pi  x _A _B  ) = M.Pi  x (desugar _A) (desugar _B)
desugar (App f a      ) = M.App (desugar f) (desugar a)
desugar (Annot a _A   ) = desugar (Stmts [Stmt (Decl "x" []) (Let _A a)] "x")
desugar (Stmts stmts e) = desugarLets (desugarStmts stmts) e
desugar (Import m     ) = desugar (runIdentity m)

{-| This is the meat of the Boehm-Berarducci encoding which translates the
    `type`, `data`, and `fold` declarations to their equivalent `let`
    expression.
-}
desugarStmts :: [Stmt Identity] -> [Let]
desugarStmts stmts0 = result
  where
    result = do
    (stmtsBefore, stmt0@(Stmt decl st0), stmtsAfter0) <- zippers stmts0
    let Decl declName0 declArgs0 = decl

    {-| Given a constructor name, find:

        * the matching statement for that constructor
        * the desugared let-binding for that constructor
    -}
    let matchingDecl :: M.Var -> Maybe (Stmt Identity, Let)
        matchingDecl (M.V x0 n0) = go x0 n0 (stmt0:stmtsBefore) 0
          where
            go x n (s@(Stmt (Decl x' _) _):stmts) k
                | x == x' && n > 0 = go x (n - 1) stmts $! k + 1
                | x == x'          = do
                    l <- safeIndex (length stmtsBefore - k) result
                    return (s, l)
                | otherwise        = go x  n      stmts $! k + 1
            go _  _   []                             _
                                   = Nothing

    let cons = do
            (_, conName, conNamesAfter) <- zippers (conNames stmts0)
            return (Var (conName `isPrecededBy` conNamesAfter))

    {- The purpose of `conArgs` is to correctly assign De Bruijn indices to
       constructor arguments.  For typical code all names will be unique and the
       DeBruijn indices will all be zero.  However, Annah permits duplicate
       names for constructors and their parameters, which results in non-zero
       DeBruijn indices.

       One case where this is useful is when the user doesn't feel like naming
       fields and just gives every field the empty label, like this example:

           type Pair (a : *) (b : *) : *
           data MkPair (_ : a) (_ : b) : Pair a b
           in   MkPair

       That will compile to this expression:

               \(a : *)
           ->  \(b : *)
           ->  \(_ : a)
           ->  \(_ : b)
           ->  \(Pair : *)
           ->  \(MkPair : a -> b -> Pair)
           ->  MkPair _@1 _

        Notice how the generated expression uses the DeBruijn index to
        distinguish the duplicate field names.
    -}
    let conArgs = do
            (_, arg, argsAfter) <- zippers declArgs0
            case st0 of
                Type -> guard (argName arg == "_")
                _    -> return ()
            let names1 = map argName argsAfter
            let names2 = conNames stmts0
            let v      = argName arg `isPrecededBy` (names1 ++ names2)
            let m = do
                    (f, _) <- unapply (argType arg)
                    matchingDecl f
            return (case m of
                Nothing -> Var v
                _       -> apply v cons )

    {- We also need to correctly compute the DeBruin index for the constructor.
       `annah` permits data constructors to have duplicate names and `annah`
       also permits data constructors to share the same name as type
       constructors.  This means that this is syntactically valid code:

           type A : *
           data A : A
           data A : A@1
           in   A

       ... which compiles to:

           \(A : *) -> \(A : A) -> \(A : A@1) -> A

       Needless to say, this is bad style, but I still permit it.
    -}
    let con = declName0 `isPrecededBy` conNames stmtsAfter0

    let reType t = case m of
            Nothing -> t
            Just t' -> t'
          where
            m = do
                (f, as) <- unapply t
                (Stmt (Decl _ args) _, _) <- matchingDecl f
                let as' = do
                        (a, Arg "_" _) <- zip as args
                        return a
                return (apply f as')

    let makeRhs piOrLam = foldr
            (\(Stmt (Decl c ps) st) ->
                let (t', ps') = case st of
                        Type   -> (Const M.Star, filter (not . namedArg) ps)
                        Data t -> (reType t, do
                            Arg x _A <- ps
                            return (Arg x (reType _A)) )
                        -- TODO: Make this total
                in  piOrLam c (pi ps' t') )
            (apply con conArgs)
            (filter (isCons . stmtType) stmts0)

    let declArgs' = do
            Arg x _A <- declArgs0
            let m = do
                    (f, as) <- unapply _A
                    (Stmt (Decl _ params) _, LetOnly _ _ rhs) <- matchingDecl f
                    let (args, e) = unPi rhs
                    (f', _) <- unapply e
                    let as' = do
                            (a, Arg "_" _) <- zip as params
                            return a
                    let e' = apply f' as'
                    return (pi args e')
            let _A' = case m of
                    Just _A' -> _A'
                    Nothing  -> _A
            return (Arg x _A')

    return (case st0 of
        Fold    -> case declArgs0 of
            [Arg x _A] -> case m of
                Just (Stmt (Decl _ args) _, LetOnly _ _ rhs') ->
                    LetOnly lhs declType' rhs
                  where
                    declType' = pi declArgs0 rhs'
                    lhs = Decl declName0 args
                    rhs = Lam x rhs' (Var (M.V x 0))
              where
                m = do
                    (f, _) <- unapply _A
                    matchingDecl f
                -- TODO: Better error handling
        Type              -> LetOnly decl (Const M.Star) rhs
          where
            rhs = makeRhs Pi
        Let  declType rhs -> LetOnly decl declType  rhs
        Data declType     -> LetOnly lhs  declType' rhs
          where
            rhs = lam declArgs' (makeRhs Lam)

            declType' = pi declArgs0 declType

            m = do
                (f, _) <- unapply declType
                matchingDecl f

            lhs = case m of
                Just (Stmt (Decl _ args) _, _) ->
                    Decl declName0 (filter namedArg args) )
                -- TODO: Proper error handling

namedArg :: Arg m -> Bool
namedArg a = argName a /= "_"

-- | Returns `True` if the given `StmtType` is a type or data constructor
isCons :: StmtType m -> Bool
isCons  Type    = True
isCons (Data _) = True
isCons  _       = False

-- | The names of all type or data constructors
conNames :: [Stmt m] -> [Text]
conNames = map (declName . stmtDecl) . filter (isCons . stmtType)

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
    n' = n + 1

{-| Compute the correct DeBruijn index for a synthetic `Var` (`x`) by providing
    all variables bound in between when `x` is introduced and when `x` is used.
-}
isPrecededBy :: Text -> [Text] -> M.Var
x `isPrecededBy` vars = M.V x (length (filter (== x) vars))

pi :: [Arg m] -> Expr m -> Expr m
pi args e = foldr (\(Arg x _A) -> Pi x _A) e args

unPi :: Expr m -> ([Arg m], Expr m)
unPi (Pi x _A _B) = (Arg x _A:args, e)
  where
    ~(args, e) = unPi _B
unPi  e           = ([], e)

lam :: [Arg m] -> Expr m -> Expr m
lam args e = foldr (\(Arg x _A) -> Lam x _A) e args

unLam :: Expr m -> ([Arg m], Expr m)
unLam (Lam x _A b) = (Arg x _A:args, e)
  where
    ~(args, e) = unLam b
unLam  e           = ([], e)

{-| This is the intermediate type that `Stmt` desugars to.

    This is essentially a `let`-only subset of `Stmt` since all `data` and
    `type` statements can be translated to `let`s.
-}
data Let = LetOnly (Decl Identity) (Expr Identity) (Expr Identity)

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
desugarLets :: [Let] -> Expr Identity -> M.Expr
desugarLets lets e = apps
  where
    -- > (   \(f0 : forall (x00 : _A00) -> ... -> forall (x0j : _A0j) -> _B0)
    -- > ->  ...
    -- > ->  \(fi : forall (xi0 : _Ai0) -> ... -> forall (xij : _Aij) -> _Bi)
    -- > ->  e
    -- > )
    lams = foldr
        (\(LetOnly (Decl fn args) _Bn _) rest ->
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
        (\(LetOnly (Decl _ args) _ bn) rest ->
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

{-| Convert a Morte expression to an Annah expression

    Right now this desugaring is trivial, but it will start to become useful
    when I add syntactic sugar for natural numbers and anonymous records
-}
resugar :: M.Expr -> Expr m
resugar (M.Const c    ) = Const c
resugar (M.Var v      ) = Var v
resugar (M.Lam x _A  b) = Lam x (resugar _A) (resugar  b)
resugar (M.Pi  x _A _B) = Pi  x (resugar _A) (resugar _B)
resugar (M.App f0 a0  ) = App (resugar f0) (resugar a0)

-- | Render a pretty-printed `Arg` as a `Builder`
buildArg :: Arg Identity -> Builder
buildArg (Arg x _A) = "(" <> fromLazyText x <> " : " <> buildExpr _A <> ")"

-- | Render a pretty-printed `Decl` as a `Builder`
buildDecl :: Decl Identity -> Builder
buildDecl (Decl x args)
    =   fromLazyText x
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)

-- | Render a pretty-printed `Stmt` as a `Builder`
buildStmt :: Stmt Identity -> Builder
buildStmt (Stmt d  Type    ) =
    "type " <> buildDecl d                                                <> " "
buildStmt (Stmt d (Data a )) =
    "data " <> buildDecl d <> ": " <> buildExpr a                         <> " "
buildStmt (Stmt d  Fold    ) =
    "fold " <> buildDecl d                                                <> " "
buildStmt (Stmt d (Let a b)) =
    "let "  <> buildDecl d <> ": " <> buildExpr a <> " = " <> buildExpr b <> " "

-- | Render a pretty-printed `Expr` as a `Builder`
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
        Import m       -> go prec (runIdentity m)
      where
        quoteAbove :: Int -> Builder -> Builder
        quoteAbove n b = if prec > n then "(" <> b <> ")" else b

{-| Pretty-print an expression

    The result is a syntactically valid Annah program
-}
prettyExpr :: Expr Identity -> Text
prettyExpr = toLazyText . buildExpr
