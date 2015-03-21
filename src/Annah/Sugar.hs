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
import Data.Char (chr, ord)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
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
desugar (MultiLam m         ) = desugarMultiLambda m
desugar (Lets ls e          ) = desugarLets  ls               e
desugar (Fam f e            ) = desugarLets (desugarFamily f) e
desugar (Natural n          ) = desugarNat n
desugar (ASCII txt          ) = desugarASCII txt
desugar (ProductValue fs    ) = desugarProductValueSection fs
desugar (ProductType  as    ) = desugarProductTypeSection as
desugar (Import m           ) = desugar (runIdentity m)

-- | Convert a Morte expression to an Annah expression
resugar :: M.Expr -> Expr m
resugar e | Just e' <- fmap Natural      (resugarNat                 e)
                   <|> fmap ProductValue (resugarProductValueSection e)
                   <|> fmap ProductType  (resugarProductTypeSection  e)
                   <|> fmap ASCII        (resugarASCII               e)
                   <|> fmap MultiLam     (resugarMultiLambda         e)
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

-- | Convert an ASCII literal to a Morte expression
desugarASCII :: Text -> M.Expr
desugarASCII txt = M.Lam "S" (M.Const M.Star) (M.Lam "N" "S" (go (0 :: Int)))
  where
    go n | n < 128   = M.Lam "C" (M.Pi "_" "S" "S") (go $! n + 1)
         | otherwise = Text.foldr cons nil txt

    cons c t = M.App (M.Var (M.V "C" (ord c))) t
    nil      = "N"

-- | Convert a Morte expression back into an ASCII literal
resugarASCII :: M.Expr -> Maybe Text
resugarASCII (M.Lam "S" (M.Const M.Star) (M.Lam "N" "S" e0)) =
    fmap Text.pack (go0 e0 (0 :: Int))
  where
    go0 (M.Lam "C" (M.Pi "_" "S" "S") e) n | n < 128 = go0 e $! n + 1
    go0 e 128                                        = go1 e
    go0 _ _                                          = empty

    go1 (M.App (M.Var (M.V "C" n)) e) = fmap (chr n:) (go1 e)
    go1 (M.Var (M.V "N" 0))           = pure []
    go1  _                            = empty
resugarASCII _ = empty

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
resugarProductValue :: M.Expr -> Maybe [ProductValueField m]
resugarProductValue
    (M.Lam "Product" (M.Const M.Star) (M.Lam "MakeProduct" t0 e0)) = do
        es <- fmap reverse (go0 e0)
        ts <- go1 t0
        guard (length es == length ts)
        return (zipWith ProductValueField es ts)
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

> (,1 : Nat,Bool)
> =>      \(t : *) -> -> \(f : t) -> \(f : Bool)
>     ->  \(Product : *) -> \(MakeProduct : t -> Nat -> Bool -> Product)
>     ->  MakeProduct f@1 1 f
-}
desugarProductValueSection :: [ProductValueSectionField Identity] -> M.Expr
desugarProductValueSection fs0 = go fs0 id id id numBoth numEmpties
  where
    numTypes   = length [ () | TypeValueField _ <- fs0 ]
    numEmpties = length [ () | EmptyValueField  <- fs0 ]
    numBoth    = numTypes + numEmpties

    shift = resugar . M.shift numBoth "f" . M.shift numEmpties "t" . desugar

    go  []                  diffFs diffL1 diffL2 _ _ =
        diffL1 (diffL2 (desugarProductValue (diffFs [])))
    go (ValueField    f:fs) diffFs diffL1 diffL2 m n =
        go fs (diffFs . (f':)) diffL1 diffL2 m n
      where
        ProductValueField e t = f
        f' = ProductValueField (shift e) (shift t)
    go (TypeValueField t:fs) diffFs diffL1 diffL2 m n = m' `seq`
        go fs (diffFs . (f':)) diffL1 (diffL2 . l2) m' n
      where
        m' = m - 1
        t' = shift t
        f' = ProductValueField (Var (M.V "f" m')) t'
        l2 = M.Lam "f" (desugar t')
    go (EmptyValueField :fs) diffFs diffL1 diffL2 m n = m' `seq` n' `seq`
        go fs (diffFs . (f':)) (diffL1 . l1) (diffL2 . l2) m' n'
      where
        m' = m - 1
        n' = n - 1
        f' = ProductValueField (Var (M.V "f" m')) (Var (M.V "t" n'))
        l1 = M.Lam "t" (M.Const M.Star)
        l2 = M.Lam "f" (M.Var (M.V "t" n'))

{-| Convert Morte expressions back into product value sections

    Example:

>     \(t : *) -> -> \(f : t) -> \(f : Bool)
> ->  \(Product : *) -> \(MakeProduct : t -> Nat -> Bool -> Product)
> ->  MakeProduct f@1 1 f
> =>  (,1 : Nat,Bool)
-}
resugarProductValueSection :: M.Expr -> Maybe [ProductValueSectionField m]
resugarProductValueSection e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const Star) e) i = go0 e $! i + 1
    go0                           e  i = go1 e id i i 0

    go1 (M.Lam "f" (M.Var (M.V "t" j)) e) diff n i  m | i' == j = m' `seq` i' `seq`
        go1 e diff' n i' m'
      where
        diff' = diff . (EmptyValueField:)
        i' = i - 1
        m' = m + 1
    go1 (M.Lam "f"  t                  e) diff n i  m           = m' `seq`
        go1 e diff' n i  m'
      where
        diff' = diff . (TypeValueField (resugar t):)
        m' = m + 1
    go1                                e  diff n 0  m           = do
        pvfs <- resugarProductValue e
        go2 pvfs (diff []) m n id
      where
        shift = resugar . M.shift (negate m) "f" . M.shift (negate n) "t" . desugar

        go2  [] [] 0 0 diff_ = pure (diff_ [])
        go2 (ProductValueField (Var (M.V "f" i)) (Var (M.V "t" j)):pvfs)
            (EmptyValueField                                      :pvss)
            m_ n_ diff_
            | i == m_' && j == n_' = m_' `seq` n_' `seq`
                go2 pvfs pvss m_' n_' diff_'
          where
            m_' = m_ - 1
            n_' = n_ - 1
            diff_' = diff_ . (EmptyValueField:)
        go2 (ProductValueField (Var (M.V "f" i))  t               :pvfs)
            (TypeValueField                       t'              :pvss)
            m_ n_ diff_
            | i == m_' && desugar t == desugar t' = m_' `seq`
                go2 pvfs pvss m_' n_ diff_'
          where
            m_' = m_ - 1
            diff_' = diff_ . (TypeValueField (resugar (desugar t')):)
        go2 (pvf:pvfs) pvss m_ n_ diff_ = go2 pvfs pvss m_ n_ diff_'
          where
            ProductValueField e' t' = pvf
            pvf' = ProductValueField (shift e') (shift t')
            diff_' = diff_ . (ValueField pvf':)
        go2 _ _ _ _ _ = empty

    go1                                _  _    _ _  _      = empty

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
    go (M.Pi x _A e) n = fmap (ProductTypeField x (resugar _A):) (go e $! n')
      where
        n' = if x == "Product" then n + 1 else n
    go (M.Var (M.V "Product" n')) n | (n == n') = pure []
    go  _                         _             = empty
resugarProductType _ = empty

{-| Convert a product type section to a Morte expression

    Example:

> {, Nat}  =>  forall (t : *) -> forall (Product : *) -> (t -> Nat -> Product) -> Product
-}
desugarProductTypeSection :: [ProductTypeSectionField Identity] -> M.Expr
desugarProductTypeSection fs0 = go fs0 id numEmpty
  where
    numEmpty = length [ () | EmptyTypeField <- fs0 ]

    go [] diff _ = desugarProductType (diff [])
    go (TypeField  ptf:fs) diff n = go fs (diff . (ptf':)) n
      where
        ProductTypeField x t = ptf
        ptf' = ProductTypeField x (shift t)
    go (EmptyTypeField:fs) diff n =
        M.Lam "t" (M.Const M.Star) (go fs (diff . (ptf':)) $! n')
      where
        ptf' = ProductTypeField "_" (Var (M.V "t" n'))
        n'   = n - 1

    shift = resugar . M.shift numEmpty "t" . desugar

{-| Convert a Morte expression back into a product type section

    Example:

> forall (t : *) -> forall (Product : *) -> (t -> Nat -> Product) -> Product  =>  {, Nat}
-}
resugarProductTypeSection :: M.Expr -> Maybe [ProductTypeSectionField m]
resugarProductTypeSection e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const M.Star) e) n = go0 e $! n + 1
    go0                             e  n = do
        ptfs <- resugarProductType e
        go1 ptfs id n
      where
        shift = resugar . M.shift (negate n) "t" . desugar

        go1 [] diff 0 = pure (diff [])
        go1 (ProductTypeField "_" (Var (M.V "t" i)):ptfs) diff n_ | n_' == i =
            go1 ptfs diff' n_'
          where
            diff' = diff . (EmptyTypeField:)
            n_' = n_ - 1
        go1 (ProductTypeField  x   t              :ptfs) diff n_ = go1 ptfs diff' n_
          where
            ptf = ProductTypeField x (shift t)
            diff' = diff . (TypeField ptf:)
        go1  _                                           _    _ = empty

{-| Convert a compressed lambda to a Morte expression

> \a b c -> e  =>  \a -> \b -> \c -> e
-}
desugarMultiLambda :: MultiLambda Identity -> M.Expr
desugarMultiLambda (MultiLambda args e) = desugar (lam args e)

{-| Convert a Morte expression back into a compressed lambda

> \a -> \b -> \c -> e  =>  \a b c -> e
-}
resugarMultiLambda :: M.Expr -> Maybe (MultiLambda m)
resugarMultiLambda (M.Lam x0 _A0 e0) = do
    -- Ensure that the resugared MultiLambda has at least one argument
    MultiLambda args e' <- go e0
    let arg = Arg x0 (resugar _A0)
    return (MultiLambda (arg:args) e')
  where
    go (M.Lam x _A e) = do
        MultiLambda args e' <- go e
        let arg = Arg x (resugar _A)
        return (MultiLambda (arg:args) e')
    go             e  = pure (MultiLambda [] (resugar e))
resugarMultiLambda             _  = empty

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
    desugarType
        :: Expr Identity -> Maybe ([Arg Identity], Expr Identity, Expr Identity)
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

    consVars :: [Text] -> [Expr Identity]
    consVars argNames = do
        (_, name, namesAfter) <- zippers (map consName constructors)
        return (name `isShadowedBy` (argNames ++ namesAfter))

    dataLets :: [Let Identity]
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
