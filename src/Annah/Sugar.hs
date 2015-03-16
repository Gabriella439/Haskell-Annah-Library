{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}

{-| This module contains all logic for desugaring Annah expressions to Morte and
    resugaring Morte expressions back to Annah.  I call this desugaring because
    Morte is a subset of Annah.
-}

module Annah.Sugar (
    -- * Sugar
      desugar
    , resugar
    ) where

import Control.Applicative (pure, empty, (<|>))
import Control.Monad (guard)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Text.Lazy (Text)
import qualified Morte.Core as M
import Prelude hiding (pi)

import Annah.Syntax

-- | Convert an Annah expression to a Morte expression
desugar :: Expr Identity -> M.Expr
desugar (Const c            ) = M.Const c
desugar (Var v              ) = M.Var   v
desugar (Lam x _A  b        ) = M.Lam x (desugar _A) (desugar  b)
desugar (Pi  x _A _B        ) = M.Pi  x (desugar _A) (desugar _B)
desugar (App f a            ) = M.App (desugar f) (desugar a)
desugar (Annot a _A         ) = desugar (Lets [Let "x" [] _A a] "x")
desugar (Lets ls e          ) = desugarLets  ls               e
desugar (Fam f e            ) = desugarLets (desugarFamily f) e
desugar (Natural n          ) = desugarNat n
desugar (ProductValue fs    ) = desugarProductValueSection fs
desugar (ProductType  as    ) = desugarProductType as
desugar (ProductAccessor m n) = desugarProductAccessor m n
desugar (Import m           ) = desugar (runIdentity m)

-- | Convert a Morte expression to an Annah expression
resugar :: M.Expr -> Expr m
resugar e | Just e' <- resugarNat        e
                   <|> resugarProductValue e
                   <|> fmap ProductType (resugarProductType  e)
                   <|> resugarProductAccessor e
          = e'
resugar (M.Const c    ) = Const c
resugar (M.Var v      ) = Var v
resugar (M.Lam x _A  b) = Lam x (resugar _A) (resugar  b)
resugar (M.Pi  x _A _B) = Pi  x (resugar _A) (resugar _B)
resugar (M.App f0 a0  ) = App (resugar f0) (resugar a0)

{-| Convert a numeric literal to a Morte expression

    Example:

> 3  =>  \(Nat : *) -> \(Zero : Nat) -> \(Succ : Nat) -> Succ (Succ (Succ Zero))
-}
desugarNat :: Integer -> M.Expr
desugarNat n0 =
    M.Lam "Nat" (M.Const M.Star) (
        M.Lam "Zero" "Nat" (
            M.Lam "Succ" (M.Pi "pred" "Nat" "Nat") (go n0) ) )
  where
    go n | n <= 0    = "Zero"
         | otherwise = M.App "Succ" (go $! n - 1)

{-| Convert a Morte expression back into a numeric literal

    Example:

> \(Nat : *) -> \(Zero : Nat) -> \(Succ : Nat) -> Succ (Succ (Succ Zero))  =>  3
-}
resugarNat :: M.Expr -> Maybe (Expr m)
resugarNat (
    M.Lam "Nat" (M.Const M.Star) (
        M.Lam "Zero" (M.Var (M.V "Nat" 0)) (
            M.Lam "Succ"
                  (M.Pi _ (M.Var (M.V "Nat" 0)) (M.Var (M.V "Nat" 0))) e0) ))
    = go e0 0
  where
    go (M.Var (M.V "Zero" 0))           n = pure (Natural n)
    go (M.App (M.Var (M.V "Succ" 0)) e) n = go e $! n + 1
    go  _                               _ = empty
resugarNat _ = empty

{-| Convert product values to Morte expressions

    Example:

> (True : Bool, 1 : Nat)
> =>  \(Product : *) -> \(MakeProduct : Bool -> Nat -> Product) -> MakeProduct True 1
-}
desugarProductValue :: [ProductValueField Identity] -> M.Expr
desugarProductValue fs0 =
    M.Lam "Product" (M.Const M.Star)
        (M.Lam "MakeProduct" (go0 fs0) (go1 (reverse fs0)))
  where
    go0 (ProductValueField _ t:fs) = M.Pi "_" (shiftOne (desugar t)) (go0 fs)
    go0  []                        = "Product"

    go1 (ProductValueField f _:fs) = M.App (go1 fs) (shiftBoth (desugar f))
    go1  []                        = "MakeProduct"

    -- Avoid name collisions if the user names anything `Product` or `MakeProduct`
    shiftOne  = M.shift 1 "Product"
    shiftBoth = M.shift 1 "Product" . M.shift 1 "MakeProduct"

{-| Convert Morte expressions back into product values

    Example:

> \(Product : *) -> \(MakeProduct : Bool -> Nat -> Product) -> MakeProduct True 1
> =>  (True : Bool, 1 : Nat)
-}
resugarProductValue :: M.Expr -> Maybe (Expr m)
resugarProductValue
    (M.Lam "Product" (M.Const M.Star) (M.Lam "MakeProduct" t0 e0)) = do
        es <- fmap reverse (go0 e0)
        ts <- go1 t0
        guard (length es == length ts)
        let makeField e t = Just (ProductValueField e t)
        return (ProductValue (zipWith makeField es ts))
  where
    go0 (M.App e a)                   = fmap (resugar (shiftBoth a):) (go0 e)
    go0 (M.Var (M.V "MakeProduct" _)) = pure []
    go0  _                            = empty

    go1 (M.Pi "_" t e)            = fmap (resugar (shiftOne t):) (go1 e)
    go1 (M.Var (M.V "Product" _)) = pure []
    go1  _                        = empty

    shiftOne  = M.shift (-1) "Product"
    shiftBoth = M.shift (-1) "Product" . M.shift (-1) "MakeProduct"
resugarProductValue _ = empty

{-| Convert product value sections to Morte expressions

    Example:

> (,1 : Nat,)
> =>      \(t : *) -> \(t : *) -> \(f : t@1) -> \(f : t)
>     ->  \(Product : *) -> \(MakeProduct : t@1 -> Nat -> t -> Product)
>     ->  MakeProduct f@1 1 f
-}
desugarProductValueSection :: [Maybe (ProductValueField Identity)] -> M.Expr
desugarProductValueSection ms0 = go0 ms0 id (n0 - 1)
  where
    n0 = length [ () | Nothing <- ms0 ]

    shift = resugar . M.shift n0 "t" . M.shift n0 "f" . desugar

    shiftPVF (ProductValueField e t) = ProductValueField (shift e) (shift t)

    go0 []           diff _ = go1 (desugarProductValue (diff [])) (n0 - 1)
    go0 (Just f :ms) diff n = go0 ms (diff . (shiftPVF f:))    n
    go0 (Nothing:ms) diff n = go0 ms (diff . (         f:)) $! n - 1
      where
        f = ProductValueField (Var (M.V "f" n)) (Var (M.V "t" n))

    go1 e n | n <  0    = go2 e (n0 - 1)
            | otherwise = M.Lam "t" (M.Const Star) (go1 e $! n - 1)

    go2 e n | n <  0     = e
            | otherwise = M.Lam "f" (M.Var (M.V "t" n)) (go2 e $! n - 1)

{-| Convert a product type to a Morte expression

    Example:

> {Bool, Nat}  =>  forall (Product : *) -> (Bool -> Nat -> Product) -> Product
-}
desugarProductType :: [ProductTypeField Identity] -> M.Expr
desugarProductType args0 =
    M.Pi "Product" (M.Const M.Star) (M.Pi "MakeProduct" (go args0 0) "Product")
  where
    go (ProductTypeField x _A:args) n = M.Pi x (desugar _A) (go args $! n')
      where
        n' = if x == "Product" then n + 1 else n
    go  []                          n = M.Var (M.V "Product" n)

{-| Convert a Morte expression back into a product type

    Example:

> forall (Product : *) -> (Bool -> Nat -> Product) -> Product  =>  {Bool, Nat}
-}
resugarProductType :: M.Expr -> Maybe [ProductTypeField m]
resugarProductType
    (M.Pi "Product" (M.Const M.Star) (M.Pi "MakeProduct" t0 "Product")) =
    go t0 0
  where
    go (M.Pi x _A e) n = fmap (ProductTypeField x (resugar _A):) (go e n')
      where
        n' = if x == "Product" then n + 1 else n
    go (M.Var (M.V "Product" n')) n | (n == n') = pure []
    go  _                         _             = empty
resugarProductType _ = empty

{-| Convert a product accessor into a Morte expression

    Example:

> 1of2
> =>  \(t : *) -> \(t : *) -> \(x : {t@1, t}) -> x (\(f : t@1) -> \(f : t) -> f@1)
-}
desugarProductAccessor :: Int -> Int -> M.Expr
desugarProductAccessor m n = go0 n
  where
    go0 k | k > 0     = M.Lam "t" (M.Const M.Star) (go0 $! k - 1)
          | otherwise =
        M.Lam "x"
            (desugarProductType
                [ProductTypeField "_" (Var (M.V "t" i)) | i <- [n-1,n-2..0]] )
            (M.App (M.App "x" (M.Var (M.V "t" (n - m)))) (go1 (n - 1)))

    go1 k | k >= 0    = M.Lam "f" (M.Var (M.V "t" k)) (go1 $! k - 1)
          | otherwise = M.Var (M.V "f" (n - m))

{-| Convert a Morte expression back into a product accessor

    Example:

> \(t : *) -> \(t : *) -> \(x : {t@1, t}) -> x (\(f : t@1) -> \(f : t) -> f@1)
> =>  1of2
-}
resugarProductAccessor :: M.Expr -> Maybe (Expr m)
resugarProductAccessor e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const M.Star) e)                          n =
        go0 e $! n + 1
    go0 (M.Lam "x" t (M.App (M.App "x" (M.Var (M.V "t" i))) e)) n = do
        let m = n - i
        fs <- resugarProductType t
        let checkField (ProductTypeField "_" (Var (M.V "t" k))) j = k == j
            checkField  _                                       _ = False
        guard (length fs == n && and (zipWith checkField fs [n-1,n-2..0]))
        go1 m n e (n - 1)
    go0  _                                                      _ =
        empty

    go1 m n (M.Lam "f" (M.Var (M.V "t" i)) e) k  | i == k     =
        go1 m n e $! k - 1
    go1 m n (M.Var (M.V "f" i))             (-1) | i == n - m =
        pure (ProductAccessor m n)
    go1 _ _  _                                _               =
        empty

-- | A type or data constructor
data Cons = Cons
    { consName :: Text
    , consArgs :: [Arg Identity]
    , consType :: Expr Identity
    }

{-| This is the meat of the Boehm-Berarducci encoding which translates type
    declarations into their equivalent `let` expressions.

    Annah permits data constructors to have duplicate names and Annah also
    permits data constructors to share the same name as type constructors.  A lot of
    the complexity of this code is due to avoiding name collisions.

    Constructor fields can also have duplicate field names, too.  This is particularly
    useful for constructors with multiple fields where the user omits the field name
    and defaults to @\"_\"@, like in this example:

    > given a : *
    > given b : *
    > type Pair
    > fold pair
    > data MkPair a b
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
desugarFamily fam = typeLets ++ dataLets ++ foldLets
  where
    universalArgs :: [Arg Identity]
    universalArgs = do
        given <- familyGivens fam
        return (Arg given (Const M.Star))

    universalVars :: [Expr Identity]
    universalVars = do
        given <- familyGivens fam
        return (Var (M.V given 0))
        -- TODO: Fix this to avoid name collisions with universal variables

    typeConstructors :: [Cons]
    typeConstructors = do
        t <- familyTypes fam
        return (Cons (typeName t) [] (Const M.Star))

    dataConstructors :: [Cons]
    dataConstructors = do
        (_       , t, tsAfter) <- zippers (familyTypes fam)
        (dsBefore, d, _      ) <- zippers (typeDatas t)
        let names1  = map typeName tsAfter
        let names2  = map dataName dsBefore
        let typeVar = typeName t `isShadowedBy` (names1 ++ names2)
        return (Cons (dataName d) (dataArgs d) typeVar)

    constructors :: [Cons]
    constructors = typeConstructors ++ dataConstructors

    makeRhs piOrLam con = go constructors
      where
        go ((Cons x args _A):stmts) = piOrLam x (pi args _A) (go stmts)
        go  []                      = con

    typeLets, foldLets :: [Let Identity]
    (typeLets, foldLets) = unzip (do
        let folds = map typeFold (familyTypes fam)
        ((_, t, tsAfter), fold) <- zip (zippers typeConstructors) folds
        let names1    = map consName tsAfter
        let names2    = map consName dataConstructors
        let con       = consName t `isShadowedBy` (names1 ++ names2)
        let typeName' = consName t
        let typeRhs'  = makeRhs Pi con
        let foldType' = Pi "x" (apply con universalVars) typeRhs'
        let foldRhs'  = Lam "x" typeRhs' "x"
        return ( Let typeName' universalArgs (consType t) typeRhs'
               , Let fold      universalArgs  foldType'   foldRhs'
               ) )

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
-- TODO: No need to return the left prefix any longer
