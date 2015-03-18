{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Importing external expressions

module Annah.Import (
    -- * Import
      load
    , Load(..)
    ) where

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Control.Monad.Trans.State.Strict (StateT, evalStateT)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Text.Lazy (Text)

import Annah.Syntax

-- | Extend `IO` with `StateT` to cache previously imported expressions
newtype Load a = Load { unLoad :: StateT (HashMap Text (Expr Load)) IO a }
    deriving (Functor, Applicative, Monad)

-- | Evaluate all `Import`s, leaving behind a pure expression
load :: Expr Load -> IO (Expr m)
load e = evalStateT (unLoad (loadExpr e)) HashMap.empty

loadExpr :: Expr Load -> Load (Expr m)
loadExpr (Const c            ) = pure (Const c)
loadExpr (Var v              ) = pure (Var v)
loadExpr (Lam x _A  b        ) = Lam x <$> loadExpr _A <*> loadExpr  b
loadExpr (Pi  x _A _B        ) = Pi  x <$> loadExpr _A <*> loadExpr _B
loadExpr (App f a            ) = App <$> loadExpr f <*> loadExpr a
loadExpr (Annot a _A         ) = Annot <$> loadExpr a <*> loadExpr _A
loadExpr (MultiLam m         ) = MultiLam <$> loadMultiLambda m
loadExpr (Lets ls e          ) = Lets <$> mapM loadLet ls <*> loadExpr e
loadExpr (Fam f e            ) = Fam <$> loadFamily f <*> loadExpr e
loadExpr (Natural n          ) = pure (Natural n)
loadExpr (ProductValue fs    ) = ProductValue <$> mapM loadProductValueSectionField fs
loadExpr (ProductType  as    ) = ProductType <$> mapM loadProductTypeSectionField as
loadExpr (Import io          ) = io >>= loadExpr

loadFamily :: Family Load -> Load (Family m)
loadFamily (Family as bs) = Family as <$> mapM loadType bs

loadType :: Type Load -> Load (Type m)
loadType (Type a b cs) = Type a b <$> mapM loadData cs

loadData :: Data Load -> Load (Data m)
loadData (Data a bs) = Data a <$> mapM loadArg bs

loadLet :: Let Load -> Load (Let m)
loadLet (Let f args _B b) =
    Let f <$> mapM loadArg args <*> loadExpr _B <*> loadExpr b

loadArg :: Arg Load -> Load (Arg m)
loadArg (Arg x _A) = Arg x <$> loadExpr _A

loadProductTypeField :: ProductTypeField Load -> Load (ProductTypeField m)
loadProductTypeField (ProductTypeField x _A) =
    ProductTypeField x <$> loadExpr _A

loadProductTypeSectionField
    :: ProductTypeSectionField Load -> Load (ProductTypeSectionField m)
loadProductTypeSectionField (TypeField a   ) = TypeField <$> loadProductTypeField a
loadProductTypeSectionField  EmptyTypeField  = pure EmptyTypeField

loadProductValueField :: ProductValueField Load -> Load (ProductValueField m)
loadProductValueField (ProductValueField a b) =
    ProductValueField <$> loadExpr a <*> loadExpr b

loadProductValueSectionField
    :: ProductValueSectionField Load -> Load (ProductValueSectionField m)
loadProductValueSectionField (ValueField     a) = ValueField <$> loadProductValueField a
loadProductValueSectionField (TypeValueField a) = TypeValueField <$> loadExpr a
loadProductValueSectionField  EmptyValueField   = pure EmptyValueField

loadMultiLambda :: MultiLambda Load -> Load (MultiLambda m)
loadMultiLambda (MultiLambda as b) = MultiLambda <$> mapM loadArg as <*> loadExpr b
