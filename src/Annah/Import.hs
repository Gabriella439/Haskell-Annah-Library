-- | Importing external expressions

module Annah.Import (
    -- * Import
      loadExpr
    ) where

import Control.Applicative (pure, (<$>), (<*>))

import Annah.Syntax

-- | Evaluate all `Import`s, leaving behind a pure expression
loadExpr :: Expr IO -> IO (Expr m)
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
loadExpr (ProductAccessor m n) = pure (ProductAccessor m n)
loadExpr (Import io          ) = io >>= loadExpr

loadFamily :: Family IO -> IO (Family m)
loadFamily (Family as bs) = Family as <$> mapM loadType bs

loadType :: Type IO -> IO (Type m)
loadType (Type a b cs) = Type a b <$> mapM loadData cs

loadData :: Data IO -> IO (Data m)
loadData (Data a bs) = Data a <$> mapM loadArg bs

loadLet :: Let IO -> IO (Let m)
loadLet (Let f args _B b) =
    Let f <$> mapM loadArg args <*> loadExpr _B <*> loadExpr b

loadArg :: Arg IO -> IO (Arg m)
loadArg (Arg x _A) = Arg x <$> loadExpr _A

loadProductTypeField :: ProductTypeField IO -> IO (ProductTypeField m)
loadProductTypeField (ProductTypeField x _A) =
    ProductTypeField x <$> loadExpr _A

loadProductTypeSectionField
    :: ProductTypeSectionField IO -> IO (ProductTypeSectionField m)
loadProductTypeSectionField (TypeField a   ) = TypeField <$> loadProductTypeField a
loadProductTypeSectionField  EmptyTypeField  = pure EmptyTypeField

loadProductValueField :: ProductValueField IO -> IO (ProductValueField m)
loadProductValueField (ProductValueField a b) =
    ProductValueField <$> loadExpr a <*> loadExpr b

loadProductValueSectionField
    :: ProductValueSectionField IO -> IO (ProductValueSectionField m)
loadProductValueSectionField (ValueField     a) = ValueField <$> loadProductValueField a
loadProductValueSectionField (TypeValueField a) = TypeValueField <$> loadExpr a
loadProductValueSectionField  EmptyValueField   = pure EmptyValueField

loadMultiLambda :: MultiLambda IO -> IO (MultiLambda m)
loadMultiLambda (MultiLambda as b) = MultiLambda <$> mapM loadArg as <*> loadExpr b
