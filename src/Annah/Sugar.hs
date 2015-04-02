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
    , static
    , dynamic
    ) where

import Control.Applicative (pure, empty, (<|>))
import Control.Monad (guard)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Char (chr, ord)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Data.Void (Void, absurd)
import qualified Morte.Core as M
import Turtle (FilePath)
import Prelude hiding (FilePath, pi)

import Annah.Syntax

-- | Convert an Annah expression to a Morte expression
desugar :: Expr Void -> M.Expr
desugar (Const c            ) = M.Const c
desugar (Var v              ) = M.Var   v
desugar (Lam x _A  b        ) = M.Lam x (desugar _A) (desugar  b)
desugar (Pi  x _A _B        ) = M.Pi  x (desugar _A) (desugar _B)
desugar (App f a            ) = M.App (desugar f) (desugar a)
desugar (Annot a _A         ) = desugar (Lets [Let "x" [] _A a] "x")
desugar (Lets ls e          ) = desugarLets  ls               e
desugar (Fam f e            ) = desugarLets (desugarFamily f) e
desugar (Natural n          ) = desugarNat n
desugar (ASCII txt          ) = desugarASCII txt
desugar (SumConstructor m n ) = desugarSumConstructor m n
desugar (SumType ts         ) = desugarSumTypeSection ts
desugar (ProductValue fs    ) = desugarProductValueSection fs
desugar (ProductType  as    ) = desugarProductTypeSection as
desugar (List t es          ) = desugarList t es
desugar (Path t oms o       ) = desugarPath t oms o
desugar (Import m           ) = absurd m

-- | Convert a Morte expression to an Annah expression
resugar :: (M.Expr -> Maybe m) -> M.Expr -> Expr m
resugar link e
    | Just e' <-  fmap Natural      (resugarNat                      e)
              <|> fmap ProductValue (resugarProductValueSection link e)
              <|> fmap ProductType  (resugarProductTypeSection  link e)
              <|> fmap ASCII        (resugarASCII                    e)
              <|> fmap sc           (resugarSumConstructor           e)
              <|> fmap list         (resugarList                link e)
              <|> fmap path         (resugarPath                link e)
              <|> fmap SumType      (resugarSumTypeSection      link e)
              <|> fmap Import       (link                            e)
    = e'
  where
    sc   (x, y)    = SumConstructor x y
    list (x, y)    = List           x y
    path (x, y, z) = Path           x y z
resugar _ (M.Const c    ) = Const c
resugar _ (M.Var v      ) = Var v
resugar link (M.Lam x _A  b) = Lam x (resugar link _A) (resugar link  b)
resugar link (M.Pi  x _A _B) = Pi  x (resugar link _A) (resugar link _B)
resugar link (M.App f a    ) = App (resugar link f) (resugar link a)

toBin :: Integer -> [Bool]
toBin n0 = reverse (go n0)
  where
    go n | n <= 0    = []
         | m == 0    = False:go d
         | otherwise = True :go d
      where
        (d, m) = n `quotRem` 2

fromBin :: [Bool] -> Integer
fromBin bs0 = go (reverse bs0) 0 1
  where
    go  []        m _ =  m
    go (False:bs) m n =  go bs    m      $! 2 * n
    go (True :bs) m n = (go bs $! m + n) $! 2 * n

-- | Convert a numeric literal to a Morte expression
desugarNat :: Integer -> M.Expr
desugarNat n0 =
    M.Lam "Bin" (M.Const M.Star)
        (M.Lam "Zero" "Bin"
            (M.Lam "One" (M.Pi "_" bin_ "Bin") (go0 (toBin n0)) ) )
  where
    bin_ =
        M.Pi "Bin_" (M.Const M.Star)
            (M.Pi "Nil_" "Bin_"
                (M.Pi "Zero_" (M.Pi "_" "Bin_" "Bin_")
                    (M.Pi "One_" (M.Pi "_" "Bin_" "Bin_")
                        "Bin_" ) ) )

    go0  []    = "Zero"
    go0 (_:bs) =
        M.App "One"
            (M.Lam "Bin_" (M.Const M.Star)
                (M.Lam "Nil_" "Bin_"
                    (M.Lam "Zero_" (M.Pi "_" "Bin_" "Bin_")
                        (M.Lam "One_" (M.Pi "_" "Bin_" "Bin_")
                            (go1 bs) ) ) ) )

    go1  []        = "Nil_"
    go1 (False:bs) = M.App "Zero_" (go1 bs)
    go1 (True :bs) = M.App "One_"  (go1 bs)

-- | Convert a Morte expression back into a numeric literal
resugarNat :: M.Expr -> Maybe Integer
resugarNat
    (M.Lam "Bin" (M.Const M.Star)
        (M.Lam "Zero" (M.Var (M.V "Bin" 0))
            (M.Lam "One"
                (M.Pi "_"
                    (M.Pi "Bin_" (M.Const M.Star)
                        (M.Pi "Nil_" (M.Var (M.V "Bin_" 0))
                            (M.Pi "Zero_"
                                (M.Pi "_"
                                    (M.Var (M.V "Bin_" 0))
                                    (M.Var (M.V "Bin_" 0))
                                )
                                (M.Pi "One_"
                                    (M.Pi "_"
                                        (M.Var (M.V "Bin_" 0))
                                        (M.Var (M.V "Bin_" 0))
                                    )
                                    (M.Var (M.V "Bin_" 0)) ) ) ) )
                    (M.Var (M.V "Bin" 0)) )
                e0 ) ) ) = do
    bs <- go0 e0
    return (fromBin bs)
  where
    go0 (M.Var (M.V "Zero" 0))          = pure []
    go0 (M.App (M.Var (M.V "One" 0))
            (M.Lam "Bin_" (M.Const M.Star)
                (M.Lam "Nil_" (M.Var (M.V "Bin_" 0))
                    (M.Lam "Zero_"
                        (M.Pi "_" (M.Var (M.V "Bin_" 0)) (M.Var (M.V "Bin_" 0)))
                        (M.Lam "One_"
                            (M.Pi "_" (M.Var (M.V "Bin_" 0))
                                (M.Var (M.V "Bin_" 0)) )
                            e ) ) ) ) ) = fmap (True:) (go1 e)
    go0 _ = empty

    go1 (M.Var (M.V "Nil_" 0))            = pure []
    go1 (M.App (M.Var (M.V "Zero_" 0)) e) = fmap (False:) (go1 e)
    go1 (M.App (M.Var (M.V "One_"  0)) e) = fmap (True :) (go1 e)
    go1 _ = empty
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

-- | Convert a sum constructor to a Morte expression
desugarSumConstructor :: Int -> Int -> M.Expr
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

-- | Convert a Morte expression back into a sum constructor
resugarSumConstructor :: M.Expr -> Maybe (Int, Int)
resugarSumConstructor e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const M.Star) e) n = go0 e $! n + 1
    go0 (M.Lam "x" (M.Var (M.V "t" i))
            (M.Lam "Sum" (M.Const M.Star) e)) n0 = go1 e 1
      where
        m0 = n0 - i

        go1 (M.Lam "MkSum" (M.Pi "x" (M.Var (M.V "t" j)) "Sum") e') n
            | j == n0 - n  = go1 e' $! n + 1
        go1 (M.App (M.Var (M.V "MkSum" j)) (M.Var (M.V "x" 0))) _
            | j == n0 - m0 = pure (m0, n0)
        go1 _ _ = empty
    go0 _ _ = empty

-- | Convert a sum type to a Morte expression
desugarSumType :: [Expr Void] -> M.Expr
desugarSumType ts0 = M.Pi "Sum" (M.Const M.Star) (go ts0 0)
  where
    go (t:ts) n = M.Pi "MkSum" (M.Pi "x" t' "Sum") (go ts $! n + 1)
      where
        t' = (M.shift 1 "Sum" . M.shift n "MkSum" . desugar) t
    go  []    _ = "Sum"

-- | Convert a Morte expression back into a sum type
resugarSumType :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [Expr m]
resugarSumType link (M.Pi "Sum" (M.Const M.Star) e0) = go id e0 0
  where
    go diff (M.Pi "MkSum" (M.Pi "x" t "Sum") e) n = go (diff . (t':)) e $! n + 1
      where
        t' = (resugar link . M.shift (-1) "Sum" . M.shift (negate n) "MkSum") t
    go diff (M.Var (M.V "Sum" 0))               _ = pure (diff [])
    go _ _ _ = empty
resugarSumType _ _ = empty

-- | Convert a sum type section to a Morte expression
desugarSumTypeSection :: [SumTypeSectionField Void] -> M.Expr
desugarSumTypeSection fs0 = go fs0 id n0
  where
    n0 = length [ () | EmptySumTypeField <- fs0 ]

    go  []                    diff _ = desugarSumType (diff [])
    go (EmptySumTypeField:fs) diff n =
        M.Lam "t" (M.Const M.Star) (go fs (diff . (t:)) $! n')
      where
        n' = n - 1
        t  = Var (M.V "t" n')
    go (SumTypeField    t:fs) diff n = go fs (diff . (shift t:)) n
      where
        shift = resugar static . M.shift n0 "t" . desugar

-- | Convert a Morte expression back into a sum type section
resugarSumTypeSection
    :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [SumTypeSectionField m]
resugarSumTypeSection link e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const M.Star) e) n0 = go0 e $! n0 + 1
    go0                             e  n0 = do
        fs <- resugarSumType static e
        go1 fs n0
      where
        go1  []                  0           = pure []
        go1 (Var (M.V "t" i):fs) m | i == m' =
            fmap (EmptySumTypeField:) (go1 fs m')
          where
            m' = m - 1
        go1 (f:fs) m = fmap (SumTypeField (shift f):) (go1 fs m)
          where
            shift = resugar link . M.shift (negate n0) "t" . desugar
        go1 _ _ = empty

{-| Convert product values to Morte expressions

    Example:

> (True : Bool, 1 : Nat)
> =>  \(Product : *) -> \(MakeProduct : Bool -> Nat -> Product) -> MakeProduct True 1
-}
desugarProductValue :: [ProductValueField Void] -> M.Expr
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
resugarProductValue
    :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [ProductValueField m]
resugarProductValue link
    (M.Lam "Product" (M.Const M.Star) (M.Lam "MakeProduct" t0 e0)) = do
        es <- fmap reverse (go0 e0)
        ts <- go1 t0
        guard (length es == length ts)
        return (zipWith ProductValueField es ts)
  where
    go0 (M.App e a)                   = fmap (resugar link (shiftBoth a):) (go0 e)
    go0 (M.Var (M.V "MakeProduct" _)) = pure []
    go0  _                            = empty

    go1 (M.Pi "_" t e)            = fmap (resugar link (shiftOne t):) (go1 e)
    go1 (M.Var (M.V "Product" _)) = pure []
    go1  _                        = empty

    shiftOne  = M.shift (-1) "Product"
    shiftBoth = M.shift (-1) "Product" . M.shift (-1) "MakeProduct"
resugarProductValue _ _ = empty

{-| Convert product value sections to Morte expressions

    Example:

> (,1 : Nat,Bool)
> =>      \(t : *) -> -> \(f : t) -> \(f : Bool)
>     ->  \(Product : *) -> \(MakeProduct : t -> Nat -> Bool -> Product)
>     ->  MakeProduct f@1 1 f
-}
desugarProductValueSection :: [ProductValueSectionField Void] -> M.Expr
desugarProductValueSection fs0 = go fs0 id id id numBoth numEmpties
  where
    numTypes   = length [ () | TypeValueField _ <- fs0 ]
    numEmpties = length [ () | EmptyValueField  <- fs0 ]
    numBoth    = numTypes + numEmpties

    shift =
        resugar static . M.shift numBoth "f" . M.shift numEmpties "t" . desugar

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
resugarProductValueSection
    :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [ProductValueSectionField m]
resugarProductValueSection link e0 = go0 e0 0
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
        diff' = diff . (TypeValueField (resugar static t):)
        m' = m + 1
    go1                                e  diff n 0  m           = do
        pvfs <- resugarProductValue static e
        go2 pvfs (diff []) m n id
      where
        shift = resugar link . M.shift (negate m) "f" . M.shift (negate n) "t" . desugar

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
            diff_' = diff_ . (TypeValueField (resugar link (desugar t')):)
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
desugarProductType :: [ProductTypeField Void] -> M.Expr
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
resugarProductType :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [ProductTypeField m]
resugarProductType link
    (M.Pi "Product" (M.Const M.Star) (M.Pi "MakeProduct" t0 "Product")) =
    go t0 0
  where
    go (M.Pi x _A e) n = fmap (ProductTypeField x (resugar link _A):) (go e $! n')
      where
        n' = if x == "Product" then n + 1 else n
    go (M.Var (M.V "Product" n')) n | (n == n') = pure []
    go  _                         _             = empty
resugarProductType _ _ = empty

{-| Convert a product type section to a Morte expression

    Example:

> {, Nat}  =>  forall (t : *) -> forall (Product : *) -> (t -> Nat -> Product) -> Product
-}
desugarProductTypeSection :: [ProductTypeSectionField Void] -> M.Expr
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

    shift = resugar static . M.shift numEmpty "t" . desugar

{-| Convert a Morte expression back into a product type section

    Example:

> forall (t : *) -> forall (Product : *) -> (t -> Nat -> Product) -> Product  =>  {, Nat}
-}
resugarProductTypeSection
    :: (M.Expr -> Maybe m) -> M.Expr -> Maybe [ProductTypeSectionField m]
resugarProductTypeSection link e0 = go0 e0 0
  where
    go0 (M.Lam "t" (M.Const M.Star) e) n = go0 e $! n + 1
    go0                             e  n = do
        ptfs <- resugarProductType static e
        go1 ptfs id n
      where
        shift = resugar link . M.shift (negate n) "t" . desugar

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

{-| Convert a list into a Morte expression

    Example:

> [* Bool, True, False]
> =>  λ(List : *)
> →   λ(Cons : ∀(head : Bool}) → ∀(tail : List) → List)
> →   λ(Nil : List)
> →   Cons True (Cons False Nil)
-}
desugarList :: Expr Void -> [Expr Void] -> M.Expr
desugarList e0 ts0 =
    M.Lam "List" (M.Const Star)
        (M.Lam "Cons" (M.Pi "head" (desugar0 e0) (M.Pi "tail" "List" "List"))
            (M.Lam "Nil" "List" (go ts0)) )
  where
    go  []    = "Nil"
    go (t:ts) = M.App (M.App "Cons" (desugar1 t)) (go ts)

    desugar0 = M.shift 1 "List" . desugar

    desugar1 = M.shift 1 "List" . M.shift 1 "Cons" . M.shift 1 "Nil" . desugar

resugarList :: (M.Expr -> Maybe m) -> M.Expr -> Maybe (Expr m, [Expr m])
resugarList link
    (M.Lam "List" (M.Const Star)
        (M.Lam "Cons"
            (M.Pi "head" e0
                (M.Pi "tail" (M.Var (M.V "List" 0)) (M.Var (M.V "List" 0))) )
            (M.Lam "Nil" (M.Var (M.V "List" 0)) ts0) ) )
    = fmap ((,) (resugar0 e0)) (go ts0)
  where
    go (M.Var (M.V "Nil" 0))                       = pure []
    go (M.App (M.App (M.Var (M.V "Cons" 0)) t) ts) = fmap (resugar1 t:) (go ts)
    go _ = empty

    resugar0 = resugar link . M.shift (-1) "List"
    resugar1 =
            resugar link
        .   M.shift (-1) "List"
        .   M.shift (-1) "Cons"
        .   M.shift (-1) "Nil"
resugarList _ _ = empty

{-| Convert a path into a Morte expression

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
    ::  Expr Void
    ->  [(Expr Void, Expr Void)]
    ->  Expr Void
    ->  M.Expr
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

resugarPath
    :: (M.Expr -> Maybe m) -> M.Expr -> Maybe (Expr m, [(Expr m, Expr m)], Expr m)
resugarPath link
    (M.Lam "Path"
        (M.Pi "a" (M.Const M.Star) (M.Pi "b" (M.Const M.Star) (M.Const M.Star)))
        (M.Lam "Step"
            (M.Pi "a" (M.Const M.Star)
                (M.Pi "b" (M.Const M.Star)
                    (M.Pi "c" (M.Const M.Star)
                        (M.Pi "head"
                            cab
                            (M.Pi "tail"
                                (M.App
                                    (M.App
                                        (M.Var (M.V "Path" 0))
                                        (M.Var (M.V "b" 0)) )
                                    (M.Var (M.V "c" 0)) )
                                (M.App
                                    (M.App
                                        (M.Var (M.V "Path" 0))
                                        (M.Var (M.V "a" 0)) )
                                    (M.Var (M.V "c" 0)) ) ) ) ) ) )
            (M.Lam "End"
                (M.Pi "a"
                    (M.Const M.Star)
                    (M.App
                        (M.App (M.Var (M.V "Path" 0)) (M.Var (M.V "a" 0)))
                        (M.Var (M.V "a" 0)) ) )
                e0 ) ) ) = do
    ((oms, o0), _) <- go e0
    let c0 = M.Lam "a" (M.Const M.Star) (M.Lam "b" (M.Const M.Star) cab)
    return (resugar0 c0, oms, resugar1 o0)
  where
    resugar0 = resugar link . M.shift (-1) "Path"
    resugar1 =
            resugar link
        .   M.shift (-1) "Path"
        .   M.shift (-1) "Step"
        .   M.shift (-1) "End"

    go (M.App (M.Var (M.V "End" 0)) o0') = return (([], o0'), o0')
    go (M.App
           (M.App
               (M.App (M.App (M.App (M.Var (M.V "Step" 0)) o1') o2') o0')
               m1' )
           e) = do
        ((oms, o0), o2) <- go e
        guard (o0 == o0' && o2 == o2')
        let o1 = resugar1 o1'
        let m1 = resugar1 m1'
        return (((o1, m1):oms, o0), o1')
    go _ = empty
resugarPath _ _ = empty

dynamic :: HashMap M.Expr FilePath -> M.Expr -> Maybe FilePath
dynamic h e = HashMap.lookup e h

static :: M.Expr -> Maybe m
static _ = empty

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
desugarLets :: [Let Void] -> Expr Void -> M.Expr
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
    , consArgs :: [Arg Void]
    , consType :: Expr Void
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
desugarFamily :: Family Void -> [Let Void]
desugarFamily fam = typeLets ++ dataLets ++ foldLets
  where
    universalArgs :: [Arg Void]
    universalArgs = familyGivens fam

    universalVars :: [Expr Void]
    universalVars = do
        Arg x _ <- familyGivens fam
        return (Var (M.V x 0))
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

    typeLets, foldLets :: [Let Void]
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
        :: Expr Void -> Maybe ([Arg Void], Expr Void, Expr Void)
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

    consVars :: [Text] -> [Expr Void]
    consVars argNames = do
        (_, name, namesAfter) <- zippers (map consName constructors)
        return (name `isShadowedBy` (argNames ++ namesAfter))

    dataLets :: [Let Void]
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
