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
    , declType :: Expr m
    }

{-| There are three types of statements:

* @type@, which creates a new type constructor
* @data@, which creates a new data constructor
* @let@, which defines a function or value in terms of another expression

    Only @let@ statements have a right-hand side
-}
data StmtType m = Type | Data | Let (Expr m)

{-| A @type@ \/ @data@ \/ @let@ declaration

> Stmt (Decl f [Arg x _A, Arg y _B] _C)  Type    ~  type f (x : _A) (y : _B) : _C
> Stmt (Decl f [Arg x _A, Arg y _B] _C)  Data    ~  data f (x : _A) (y : _B) : _C
> Stmt (Decl f [Arg x _A, Arg y _B] _C) (Let z)  ~  let  f (x : _A) (y : _B) : _C = z
-}
data Stmt m =
    Stmt { stmtDecl :: Decl m, stmtType :: StmtType m }

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
loadDecl (Decl x args _A) = Decl x <$> mapM loadArg args <*> load _A

loadStmtType :: StmtType IO -> IO (StmtType m)
loadStmtType  Type     = return Type
loadStmtType  Data     = return Data
loadStmtType (Let rhs) = Let <$> load rhs

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
desugar (Annot a _A   ) = desugar (Stmts [Stmt (Decl "x" [] _A) (Let a)] "x")
desugar (Stmts stmts e) = desugarLets (desugarStmts stmts) e
desugar (Import m     ) = desugar (runIdentity m)

{-| This is the meat of the Boehm-Berarducci encoding which translates the
    `type` or `data` declarations to their equivalent `let` expression.

    This is technically a variation on Boehm-Berarducci encoding which supports
    generalized algebraic data types (GADTs).  For example, a true
    Boehm-Berarducci encoding would encode the `Either` type constructor like
    this:

    let Either (a : *) (b : *) : *
            =   forall (Either : *)
            ->  forall (Left   : a -> Either)
            ->  forall (Right  : b -> Either)
            ->  Either

    ... whereas `annah` encodes `Either` like this:

    let Either (a : *) (b : *) : *
            =   forall (Either : * -> * -> *)
            ->  forall (Left   : a -> Either a b)
            ->  forall (Right  : b -> Either a b)
            ->  Either a b

   The reason I do things this way is because this encoding can implement GADTs.

    This function uses several naming conventions:

    * "sim"    - Simple, meaning non-recursive
    * "rec"    - Recursive
    * "con"    - Constructor
-}
desugarStmts :: [Stmt Identity] -> [Let]
desugarStmts stmts0 = result
  where
    result = do
    (stmtsBefore, Stmt decl st0, stmtsAfter0) <- zippers stmts0
    let Decl declName0 declArgs0 declType0 = decl

    {-| Given a constructor applied to 0 or more arguments, find:

        * the matching constructor declaration
        * the index of the matching statement
    -}
    let matchingDecl :: Expr Identity -> Maybe (Decl Identity, Int)
        matchingDecl v0 = do
            M.V x0 n0 <- unapply v0
            go x0 n0 stmtsBefore 0
          where
            go x n (Stmt d@(Decl x' _ _) st:stmts) k
                | x == x' && n > 0 = go x (n - 1) stmts $! k'
                | x == x'          = Just (d, length stmtsBefore - k - 1)
                | otherwise        = go x  n      stmts $! k'
                  where k' = k + (case st of Type -> 2; _ -> 1)
            go _  _   []                          _
                                   = Nothing

    let nonRecursive arg = case matchingDecl (argType arg) of
            Nothing -> True
            _       -> False
    let (simArgs, recArgs) = span nonRecursive declArgs0
    let cons = do
            (_, conName, conNamesAfter) <- zippers (conNames stmts0)
            return (conName `isPrecededBy` conNamesAfter)

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
           ->  \(Pair : * -> * -> *)
           ->  \(MkPair : a -> b -> Pair a b)
           ->  MkPair _@1 _

        Notice how the generated expression uses the DeBruijn index to
        distinguish the duplicate field names.
    -}
    let conArgs = do
            (_, arg, argsAfter) <- zippers declArgs0
            let names1 = map argName argsAfter
            let names2 = conNames stmts0
            let v      = argName arg `isPrecededBy` (names1 ++ names2)
            return (case matchingDecl (argType arg) of
                Nothing -> v
                _       -> foldr (flip App) v (reverse cons) )

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

    let saturated c = foldr (flip App) c (reverse conArgs)
    let makeRhs piOrLam = foldr
            (\(Stmt (Decl c ps t) _) -> piOrLam c (foldArgs Pi t ps))
            (saturated con)
            (keepCons stmts0)

    case st0 of
            Type    -> [LetOnly decl rhs, LetOnly foldDecl foldRhs]
              where
                -- Every type constructor `foo` comes with an eliminator named
                -- `foldfoo`
                rhs      = makeRhs Pi
                foldType = Pi "_" (saturated (Var (M.V declName0 0))) rhs
                foldDecl = Decl ("fold" <> declName0) declArgs0 foldType
                foldRhs  = Lam "x" rhs "x"
            Let rhs -> [LetOnly decl rhs]
            Data    -> [LetOnly lhs  rhs]
              where
                rhs = foldArgs Lam (makeRhs Lam) recArgs'

                recArgs' = do
                    Arg x _A <- recArgs
                    let m = do
                            (_, k) <- matchingDecl _A
                            safeIndex k result
                    let _A' = case m of
                            Just (LetOnly _ _A') -> _A'
                            -- TODO: Proper error handling
                    return (Arg x _A')

                {- Data constructors are universally quantified over all type
                   variables in their matching type constructor.

                   So, for example, if you write:

                       type Either (a : *) (b : *) : *
                       data Left  (l : a) : Either a b
                       data Right (r : b) : Either a b

                   ... the `Left` and `Right` data constructors are universally
                   quantified over `a` and `b`.

                   The following code locates the matching type constructor for
                   any data declaration and implicitly adds the type
                   constructor's parameters as additional arguments to the data
                   constructor.

                   Note that if the user adds any type variables explicitly they
                   will be existentially quantified, not universally quantified.
                   Here's an example of how the `Fold` type from Haskell's
                   `foldl` library would be encoded:

                       -- The `a` and `b` are universally quantified
                       type Fold (a : *) (b : *) : *
                       -- The `x` is existentially quantified
                       data MkFold
                                (x : *)
                                (step : x -> a -> x)
                                (begin : x)
                                (done : a -> b) : Fold a b
                -}
                lhs = case matchingDecl declType0 of
                    Just (Decl _ args _, _) -> Decl
                        declName0
                        (args ++ simArgs)
                        (foldArgs Pi declType0 recArgs)
                    -- TODO: Proper error handling

-- | Returns `True` if the given `StmtType` is a type or data constructor
isCons :: StmtType m -> Bool
isCons Type = True
isCons Data = True
isCons _    = False

-- | Keep only `Stmt`s that are type or data constructor declarations
keepCons :: [Stmt m] -> [Stmt m]
keepCons = filter (isCons . stmtType)

-- | The names of all type or data constructors
conNames :: [Stmt m] -> [Text]
conNames = map (declName . stmtDecl) . keepCons

-- | Extract a saturated type constructor's name
unapply :: Expr m -> Maybe M.Var
unapply (App e _) = unapply e
unapply (Var v  ) = Just v
unapply  _        = Nothing

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
isPrecededBy :: Text -> [Text] -> Expr m
x `isPrecededBy` vars = Var (M.V x (length (filter (== x) vars)))

{-|
> foldArgs Lam e [(Arg x0 _A0), ..., (Arg xj _Aj)]
> = "\(x0 : _A0) -> ... -> \(xj : _Aj) -> e"
>
> foldArgs Pi e [(Arg x0 _A0), ..., (Arg xj _Aj)]
> = "forall (x0 : _A0) -> ... -> forall (xj : _Aj) -> e"
-}
foldArgs :: (Text -> Expr m -> b -> b ) -> b -> [Arg m] -> b
foldArgs f = foldr (\(Arg x _A) -> f x _A)

{-| This is the intermediate type that `Stmt` desugars to.

    This is essentially a `let`-only subset of `Stmt` since all `data` and
    `type` statements can be translated to `let`s.
-}
data Let = LetOnly (Decl Identity) (Expr Identity)

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
        (\(LetOnly (Decl fn args _Bn) _) rest ->
            -- > forall (xn0 : _An0) -> ... -> forall (xnj : _Anj) -> _Bn
            let rhsType = foldArgs Pi _Bn args

            -- > \(fn : rhsType) -> rest
            in  M.Lam fn (desugar rhsType) rest )
        (desugar e)
        lets

    -- > lams
    -- > (\(x00 : _A00) -> ... -> \(x0j : _A0j) -> b0)
    -- > ...
    -- > (\(xi0 : _Ai0) -> ... -> \(xij : _Aij) -> bi)
    apps = foldr
        (\(LetOnly (Decl _ args _) bn) rest ->
            -- > rest (\(xn0 : _An0) -> ... -> \(xnj : _Anj) -> bn)
            M.App rest (desugar (foldArgs Lam bn args)) )
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
buildDecl (Decl x args _A)
    =   fromLazyText x
    <>  " "
    <>  mconcat (map (\arg -> buildArg arg <> " ") args)
    <>  ": "
    <>  buildExpr _A

-- | Render a pretty-printed `Stmt` as a `Builder`
buildStmt :: Stmt Identity -> Builder
buildStmt (Stmt d  Type  ) = "type " <> buildDecl d                         <> " "
buildStmt (Stmt d  Data  ) = "data " <> buildDecl d                         <> " "
buildStmt (Stmt d (Let a)) = "let "  <> buildDecl d <> " = " <> buildExpr a <> " "

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
