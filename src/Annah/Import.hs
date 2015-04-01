{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | Importing external expressions

module Annah.Import (
    -- * Import
      loadExpr
    , Load(..)
    ) where

import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Control.Exception (throwIO)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (unpack)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as Text
import Turtle hiding (Text)
import Prelude hiding (FilePath)

import Annah.Syntax
import Annah.Parser (exprFromText)

-- | Extend `IO` with `StateT` to cache previously imported expressions
newtype Load a = Load { unLoad :: StateT (Map FilePath (Expr FilePath)) IO a }
    deriving (Functor, Applicative, Monad)

loadExpr :: Expr FilePath -> IO (Expr m)
loadExpr e = evalStateT (unLoad (load e)) Map.empty

-- | `load` evaluates all `Import`s, leaving behind a pure expression
class Loads f where
    load :: f FilePath -> Load (f m)

instance Loads Expr where
    load (Const c            ) = pure (Const c)
    load (Var v              ) = pure (Var v)
    load (Lam x _A  b        ) = Lam x <$> load _A <*> load  b
    load (Pi  x _A _B        ) = Pi  x <$> load _A <*> load _B
    load (App f a            ) = App <$> load f <*> load a
    load (Annot a _A         ) = Annot <$> load a <*> load _A
    load (Lets ls e          ) = Lets <$> mapM load ls <*> load e
    load (Fam f e            ) = Fam <$> load f <*> load e
    load (Natural n          ) = pure (Natural n)
    load (ASCII txt          ) = pure (ASCII txt)
    load (SumConstructor m n ) = pure (SumConstructor m n)
    load (SumType ts         ) = SumType <$> mapM load ts
    load (ProductValue fs    ) = ProductValue <$> mapM load fs
    load (ProductType  as    ) = ProductType <$> mapM load as
    load (List t es          ) = List <$> load t <*> mapM load es
    load (Path c oms o0      ) = Path <$> load c <*> mapM loadP oms <*> load o0
      where
        loadP (o, m) = (,) <$> load o <*> load m
    load (Import path        ) = Load (do
        m <- get
        case Map.lookup path m of
            Just expr -> unLoad (load expr)
            Nothing   -> do
                txt <- liftIO (Text.readFile (unpack (format fp path)))
                case exprFromText txt of
                    Left pe    -> liftIO (throwIO pe)
                    Right expr -> do
                        put (Map.insert path expr m)
                        unLoad (load expr) )

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

instance Loads SumTypeSectionField where
    load (SumTypeField f   ) = SumTypeField <$> load f
    load  EmptySumTypeField  = pure EmptySumTypeField
