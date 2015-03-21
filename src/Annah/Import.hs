{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Importing external expressions

module Annah.Import (
    -- * Import
      loadExpr
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

loadExpr :: Expr Load -> IO (Expr m)
loadExpr e = evalStateT (unLoad (load e)) HashMap.empty

-- | `load` evaluates all `Import`s, leaving behind a pure expression
class Loads f where
    load :: f Load -> Load (f m)

instance Loads Expr where
    load (Const c            ) = pure (Const c)
    load (Var v              ) = pure (Var v)
    load (Lam x _A  b        ) = Lam x <$> load _A <*> load  b
    load (Pi  x _A _B        ) = Pi  x <$> load _A <*> load _B
    load (App f a            ) = App <$> load f <*> load a
    load (Annot a _A         ) = Annot <$> load a <*> load _A
    load (MultiLam m         ) = MultiLam <$> load m
    load (Lets ls e          ) = Lets <$> mapM load ls <*> load e
    load (Fam f e            ) = Fam <$> load f <*> load e
    load (Natural n          ) = pure (Natural n)
    load (ASCII txt          ) = pure (ASCII txt)
    load (SumConstructor m n ) = pure (SumConstructor m n)
    load (ProductValue fs    ) = ProductValue <$> mapM load fs
    load (ProductType  as    ) = ProductType <$> mapM load as
    load (Import io          ) = io >>= load

instance Loads Family where
    load (Family as bs) = Family <$> mapM load as <*> mapM load bs

instance Loads Type where
    load (Type a b cs) = Type a b <$> mapM load cs

instance Loads Data where
    load (Data a bs) = Data a <$> mapM load bs

instance Loads Let where
    load (Let f args _B b) = Let f <$> mapM load args <*> load _B <*> load b

instance Loads Arg where
    load (Arg x _A) = Arg x <$> load _A

instance Loads ProductTypeField where
    load (ProductTypeField x _A) = ProductTypeField x <$> load _A

instance Loads ProductTypeSectionField where
    load (TypeField a   ) = TypeField <$> load a
    load  EmptyTypeField  = pure EmptyTypeField

instance Loads ProductValueField where
    load (ProductValueField a b) = ProductValueField <$> load a <*> load b

instance Loads ProductValueSectionField where
    load (ValueField     a) = ValueField <$> load a
    load (TypeValueField a) = TypeValueField <$> load a
    load  EmptyValueField   = pure EmptyValueField

instance Loads MultiLambda where
    load (MultiLambda as b) = MultiLambda <$> mapM load as <*> load b
