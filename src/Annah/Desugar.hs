{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}
{-# OPTIONS_GHC -Wall #-}

{-| This module contains all logic for desugaring Annah expressions to Morte.
    I call this desugaring because Morte is a subset of Annah.
-}

module Annah.Desugar (
    -- * Sugar
      desugar
    ) where

import Control.Applicative (pure, empty)
import Data.Char (ord)
import Data.Monoid ((<>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Morte.Core as M
import Prelude hiding (pi)

import Annah.Syntax

-- | Convert an Annah expression to a Morte expression
desugar :: Eq a => Expr a -> M.Expr a
desugar (Const c           ) = M.Const c
desugar (Var v             ) = M.Var   v
desugar (Lam x _A  b       ) = M.Lam x (desugar _A) (desugar  b)
desugar (Pi  x _A _B       ) = M.Pi  x (desugar _A) (desugar _B)
desugar (App f a           ) = M.App (desugar f) (desugar a)
desugar (Import p          ) = M.Import p
desugar (Annot a _A        ) = desugar (Lets [Let "x" [] _A a] "x")
desugar (Lets ls e         ) = desugarLets  ls               e
desugar (Fam f e           ) = desugarLets (desugarFamily f) e
desugar (Natural n         ) = desugarNat n
desugar (ASCII txt         ) = desugarASCII txt
desugar (SumConstructor m n) = desugarSumConstructor m n
desugar (SumType ts        ) = desugarSumType ts
desugar (ProductValue fs   ) = desugarProductValue fs
desugar (ProductType  as   ) = desugarProductType as
desugar (List t es         ) = desugarList t es
desugar (ListType f        ) = desugarListType f
desugar (Path t oms o      ) = desugarPath t oms o
desugar (Do m bs b         ) = desugarDo m bs b

data Bin = Zero | One Bin_

data Bin_ = Nil_ | Zero_ Bin_ | One_ Bin_

integerToBin :: Integer -> Bin
integerToBin n0 = go0 n0
  where
    go0 n
        | n <= 0    = Zero
        | r == 0    = case go0 q of
            Zero     -> Zero
            One bin_ -> One (append Zero_ bin_)
        | otherwise = case go0 q of
            Zero     -> One Nil_
            One bin_ -> One (append One_  bin_)
      where
        (q, r) = n `quotRem` 2

    append diffBin_  Nil_        = diffBin_ Nil_
    append diffBin_ (Zero_ bin_) = Zero_ (append diffBin_ bin_)
    append diffBin_ (One_  bin_) = One_ (append diffBin_  bin_)

-- | Convert a numeric literal to a Morte expression
desugarNat :: Integer -> M.Expr a
desugarNat n0 =
    M.Lam "Bin" (M.Const M.Star)
        (M.Lam "Zero" "Bin"
            (M.Lam "One" (M.Pi "_" bin_Type "Bin") (go0 (integerToBin n0)) ) )
  where
    bin_Type =
        M.Pi "Bin_" (M.Const M.Star)
            (M.Pi "Nil_" "Bin_"
                (M.Pi "Zero_" (M.Pi "_" "Bin_" "Bin_")
                    (M.Pi "One_" (M.Pi "_" "Bin_" "Bin_")
                        "Bin_" ) ) )

    go0  Zero      = "Zero"
    go0 (One bin_) =
        M.App "One"
            (M.Lam "Bin_" (M.Const M.Star)
                (M.Lam "Nil_" "Bin_"
                    (M.Lam "Zero_" (M.Pi "_" "Bin_" "Bin_")
                        (M.Lam "One_" (M.Pi "_" "Bin_" "Bin_")
                            (go1 bin_) ) ) ) )

    go1  Nil_        = "Nil_"
    go1 (Zero_ bin_) = M.App "Zero_" (go1 bin_)
    go1 (One_  bin_) = M.App "One_"  (go1 bin_)

-- | Convert an ASCII literal to a Morte expression
desugarASCII :: Text -> M.Expr a
desugarASCII txt = M.Lam "S" (M.Const M.Star) (M.Lam "N" "S" (go (0 :: Int)))
  where
    go n | n < 128   = M.Lam "C" (M.Pi "_" "S" "S") (go $! n + 1)
         | otherwise = Text.foldr cons nil txt

    cons c t = M.App (M.Var (M.V "C" (ord c))) t
    nil      = "N"

-- | Convert a sum constructor to a Morte expression
desugarSumConstructor :: Int -> Int -> M.Expr a
desugarSumConstructor m0 n0 = go0 1
  where
    go0 n | n <= n0   = M.Lam "t" (M.Const M.Star) (go0 $! n + 1)
          | otherwise =
              M.Lam "x" (M.Var (M.V "t" (n0 - m0)))
                  (M.Lam "Sum" (M.Const M.Star) (go1 1))

    go1 n
        | n <= n0   =
            M.Lam "MkSum" (M.Pi "x" (M.Var (M.V "t" (n0 - n))) "Sum")
                (go1 $! n + 1)
        | otherwise = M.App (M.Var (M.V "MkSum" (n0 - m0))) "x"

-- | Convert a sum type to a Morte expression
desugarSumType :: Eq a => [Expr a] -> M.Expr a
desugarSumType ts0 = M.Pi "Sum" (M.Const M.Star) (go ts0 0)
  where
    go (t:ts) n = M.Pi "MkSum" (M.Pi "x" t' "Sum") (go ts $! n + 1)
      where
        t' = (M.shift 1 "Sum" . M.shift n "MkSum" . desugar) t
    go  []    _ = "Sum"

{-| Convert product values to Morte expressions

    Example:

> (True : Bool, 1 : Nat)
> =>  \(Product : *) -> \(MakeProduct : Bool -> Nat -> Product) -> MakeProduct True 1
-}
desugarProductValue :: Eq a => [ProductValueField a] -> M.Expr a
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

{-| Convert a product type to a Morte expression

    Example:

> {Bool, Nat}  =>  forall (Product : *) -> (Bool -> Nat -> Product) -> Product
-}
desugarProductType :: Eq a => [ProductTypeField a] -> M.Expr a
desugarProductType args0 =
    M.Pi "Product" (M.Const M.Star) (M.Pi "MakeProduct" (go args0 0) "Product")
  where
    go (ProductTypeField x _A:args) n = M.Pi x (desugar _A) (go args $! n')
      where
        n' = if x == "Product" then n + 1 else n
    go  []                          n = M.Var (M.V "Product" n)

{-| Convert a list into a Morte expression

    Example:

> [nil Bool, True, False]
> =>  λ(List : *)
> →   λ(Cons : ∀(head : Bool}) → ∀(tail : List) → List)
> →   λ(Nil : List)
> →   Cons True (Cons False Nil)
-}
desugarList :: Eq a => Expr a -> [Expr a] -> M.Expr a
desugarList e0 ts0 =
    M.Lam "List" (M.Const Star)
        (M.Lam "Cons" (M.Pi "head" (desugar0 e0) (M.Pi "tail" "List" "List"))
            (M.Lam "Nil" "List" (go ts0)) )
  where
    go  []    = "Nil"
    go (t:ts) = M.App (M.App "Cons" (desugar1 t)) (go ts)

    desugar0 = M.shift 1 "List" . desugar

    desugar1 = M.shift 1 "List" . M.shift 1 "Cons" . M.shift 1 "Nil" . desugar

{-| Convert a list type into a Morte expression

    Example:

> [t]
> =>  ∀(List : *)
> →   ∀(Cons : ∀(head : t) → ∀(tail : List) → List)
> →   ∀(Nil : List)
> →   List
-}
desugarListType :: Eq a => Expr a -> M.Expr a
desugarListType t =
    M.Pi "List" (M.Const M.Star)
        (M.Pi "Cons" (M.Pi "head" (desugar0 t) (M.Pi "tail" "List" "List"))
            (M.Pi "Nil" "List" "List") )
  where
    desugar0 = M.shift 1 "List" . desugar

{-| Convert a path into a Morte expression

    For the experts, a path is a \"free category\" (a.k.a. a \"type-aligned
    list\")

    Example:

> [. cat (|a|) f (|b|) g (|c|)]
> =>  λ(Path : ∀(a : *) → ∀(b : *) → *)
> →   λ(  Step
>     :   ∀(a : *)
>     →   ∀(b : *)
>     →   ∀(c : *)
>     →   ∀(head : cat a b)
>     →   ∀(tail : Path b c)
>     →   Path a c
>     )
> →   λ(End : ∀(a : *) → Path a a)
> →   Step a b c f (Step b c c g (End c))
-}
desugarPath
    ::  Eq a
    =>  Expr a
    ->  [(Expr a, Expr a)]
    ->  Expr a
    ->  M.Expr a
desugarPath c0 oms0 o0 =
    M.Lam "Path"
        (M.Pi "a" (M.Const M.Star) (M.Pi "b" (M.Const M.Star) (M.Const M.Star)))
        (M.Lam "Step"
            (M.Pi "a" (M.Const M.Star)
                (M.Pi "b" (M.Const M.Star)
                    (M.Pi "c" (M.Const M.Star)
                        (M.Pi "head" (M.App (M.App (desugar0 c0) "a") "b")
                            (M.Pi "tail" (M.App (M.App "Path" "b") "c")
                                (M.App (M.App "Path" "a") "c") ) ) ) ) )
            (M.Lam "End"
                (M.Pi "a" (M.Const M.Star) (M.App (M.App "Path" "a") "a"))
                (go oms0) ) )
  where
    desugar0 = M.shift 1 "Path" . desugar
    desugar1 = M.shift 1 "Path" . M.shift 1 "Step" . M.shift 1 "End" . desugar

    go []                         = M.App "End" (desugar1 o0)
    go [(o1, m1)]                 =
        M.App (M.App (M.App (M.App (M.App "Step" o1') o0') o0') m1') (go [] )
      where
        o0' = desugar1 o0
        o1' = desugar1 o1
        m1' = desugar1 m1
    go ((o1, m1):oms@((o2, _):_)) =
        M.App (M.App (M.App (M.App (M.App "Step" o1') o2') o0') m1') (go oms)
      where
        o0' = desugar1 o0
        o1' = desugar1 o1
        o2' = desugar1 o2
        m1' = desugar1 m1

{-| Convert a command (i.e. do-notation) into a Morte expression

    For the experts, this encodes the do-notation using what the Haskell world
    calls the \"operational monad\" which is a free monad without a functor
    constraint.  I choose this approach because Annah does not have type
    classes.

    Example:

> do m { x0 : _A0 <- e0; x1 : _A1 <- e1 }
> =>  λ(Cmd : *)
> →   λ(Bind : ∀(b : *) → m b → (b → Cmd) → Cmd)
> →   λ(Pure : ∀(x1 : _A1) → Cmd)
> →   Bind
>     _A0
>     e0
>     (   λ(x0 : _A0)
>     →   Bind
>         _A1
>         e1
>         Pure
>     )
-}
desugarDo :: Eq a => Expr a -> [Bind a] -> Bind a -> M.Expr a
desugarDo m bs0 (Bind (Arg x0 _A0) e0) =
    M.Lam "Cmd" (M.Const M.Star)
        (M.Lam "Bind"
            (M.Pi "b" (M.Const M.Star)
                (M.Pi "_" (M.App (desugar m) "b")
                    (M.Pi "_" (M.Pi "_" "b" "Cmd") "Cmd") ) )
            (M.Lam "Pure" (M.Pi x0 (desugar _A0) "Cmd")
                (go bs0 (0 :: Int) (0 :: Int)) ) )
  where
    go  []                    numPure numBind =
        M.App
            (M.App (M.App (M.Var (M.V "Bind" numBind)) (desugar _A0))
                (desugar e0) )
            (M.Var (M.V "Pure" numPure))
    go (Bind (Arg x _A) e:bs) numPure numBind = numBind' `seq` numPure' `seq`
        M.App
            (M.App
                (M.App (M.Var (M.V "Bind" numBind)) (desugar _A))
                (desugar e) )
            (M.Lam x (desugar _A) (go bs numBind' numPure'))
      where
        numBind' = if x == "Bind" then numBind + 1 else numBind
        numPure' = if x == "Pure" then numPure + 1 else numPure

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
desugarLets :: Eq a => [Let a] -> Expr a -> M.Expr a
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

-- | A type or data constructor
data Cons a = Cons
    { consName :: Text
    , consArgs :: [Arg a]
    , consType :: Expr a
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
    > data MakePair a b
    > in   MakePair

    ... which compiles to:

    >     \(a : *)
    > ->  \(b : *)
    > ->  \(_ : a)
    > ->  \(_ : b)
    > ->  \(Pair : *)
    > ->  \(MakePair : a -> b -> Pair)
    > ->  MakePair _@1 _
-}
desugarFamily :: Eq a => Family a -> [Let a]
desugarFamily fam = typeLets ++ dataLets ++ foldLets
  where
--  universalArgs :: [Arg Void]
    universalArgs = familyGivens fam

--  universalVars :: [Expr Void]
    universalVars = do
        Arg x _ <- familyGivens fam
        return (Var (M.V x 0))
        -- TODO: Fix this to avoid name collisions with universal variables

--  typeConstructors :: [Cons]
    typeConstructors = do
        t <- familyTypes fam
        return (Cons (typeName t) [] (Const M.Star))

--  dataConstructors :: [Cons]
    dataConstructors = do
        (_       , t, tsAfter) <- zippers (familyTypes fam)
        (dsBefore, d, _      ) <- zippers (typeDatas t)
        let names1  = map typeName tsAfter
        let names2  = map dataName dsBefore
        let typeVar = typeName t `isShadowedBy` (names1 ++ names2)
        return (Cons (dataName d) (dataArgs d) typeVar)

--  constructors :: [Cons]
    constructors = typeConstructors ++ dataConstructors

    makeRhs piOrLam con = go constructors
      where
        go ((Cons x args _A):stmts) = piOrLam x (pi args _A) (go stmts)
        go  []                      = con

--  typeLets, foldLets :: [Let Void]
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
--  desugarType
--      :: Expr Void -> Maybe ([Arg Void], Expr Void, Expr Void)
    desugarType (Pi x _A e      )   = do
        ~(args, f, f') <- desugarType e
        return (Arg x _A:args, f, f')
    desugarType f@(Var (M.V x0 n0)) = do
        f' <- go0 dataConstructors x0 n0
        return ([], f, f')
      where
        go0 (d:ds) x n | consName d == x =
            if n > 0 then go0 ds x $! n - 1 else empty
                       | otherwise       = go0 ds x n
        go0  []    x n                   = go1 (reverse typeLets) x n

        go1 (t:ts) x n | letName  t == x =
            if n > 0 then go1 ts x $! n - 1 else pure (letRhs t)
                       | otherwise       = go1 ts x n
        go1  []    _ _                   = empty
    desugarType _ = empty

--  consVars :: [Text] -> [Expr Void]
    consVars argNames = do
        (_, name, namesAfter) <- zippers (map consName constructors)
        return (name `isShadowedBy` (argNames ++ namesAfter))

--  dataLets :: [Let Void]
    dataLets = do
        (_, d, dsAfter) <- zippers dataConstructors
        let conVar  = consName d `isShadowedBy` map consName dsAfter
        let conArgs = do
                (_, arg, argsAfter) <- zippers (consArgs d)
                let names1 = map argName  argsAfter
                let names2 = map consName constructors
                return (case desugarType (argType arg) of
                    Nothing           -> argVar
                      where
                        names = names1 ++ names2
                        argVar = argName arg `isShadowedBy` names
                    Just (args, _, _) ->
                        lam args (apply argVar (argExprs ++ consVars names3))
                      where
                        names3 = map argName args
                        names = names1 ++ names2 ++ names3
                        argVar = argName arg `isShadowedBy` names
                        argExprs = do
                            (_, name, namesAfter) <- zippers names3
                            return (name `isShadowedBy` namesAfter) )
        let (lhsArgs, rhsArgs) = unzip (do
                arg@(Arg x _A) <- consArgs d
                return (case desugarType _A of
                    Just (args, _B, _B') -> (lhsArg, rhsArg)
                      where
                        lhsArg = Arg x (pi args (apply _B universalVars))
                        rhsArg = Arg x (pi args        _B'             )
                    Nothing              -> (   arg,    arg) ) )
        let letType' = pi  lhsArgs (apply (consType d) universalVars)
        let letRhs'  = lam rhsArgs (makeRhs Lam (apply conVar conArgs))
        return (Let (consName d) universalArgs letType' letRhs')

-- | Apply an expression to a list of arguments
apply :: Expr a -> [Expr a] -> Expr a
apply f as = foldr (flip App) f (reverse as)

{-| Compute the correct DeBruijn index for a synthetic `Var` (`x`) by providing
    all variables bound in between when `x` is introduced and when `x` is used.
-}
isShadowedBy :: Text -> [Text] -> Expr a
x `isShadowedBy` vars = Var (M.V x (length (filter (== x) vars)))

pi :: [Arg a] -> Expr a -> Expr a
pi args e = foldr (\(Arg x _A) -> Pi x _A) e args

lam :: [Arg a] -> Expr a -> Expr a
lam args e = foldr (\(Arg x _A) -> Lam x _A) e args

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
