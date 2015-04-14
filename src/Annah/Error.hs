{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}

module Annah.Error (
    -- * Error
      TypeError(..)
    , TypeMessage(..)
    , Context
    , resugarTypeError
    ) where

import Control.Exception (Exception)
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (fromLazyText, toLazyText)
import Data.Typeable (Typeable)
import qualified Morte.Core as M
import Turtle (FilePath)
import Prelude hiding (FilePath)

import Annah.Pretty (Builds(..))
import Annah.Sugar (resugar)
import Annah.Syntax (Expr)

data TypeError m = TypeError
    { context     :: Context m
    , current     :: Expr m
    , typeMessage :: TypeMessage m
    } deriving (Typeable)

instance Show (TypeError FilePath) where
    show = unpack . prettyTypeError

instance Exception (TypeError FilePath)

data TypeMessage m
    = UnboundVariable
    | InvalidInputType (Expr m)
    | InvalidOutputType (Expr m)
    | NotAFunction
    | TypeMismatch (Expr m) (Expr m)
    | Untyped M.Const

newtype Context m = Context { getContext :: [(Text, Expr m)] }

instance Show (TypeMessage FilePath) where
    show = unpack . toLazyText . build

resugarTypeError :: (M.Expr -> Maybe m) -> M.TypeError -> TypeError m
resugarTypeError link (M.TypeError ctx curr msg) = TypeError
    (resugarContext link ctx)
    (resugar link curr)
    (resugarTypeMessage link msg)

resugarTypeMessage :: (M.Expr -> Maybe m) -> M.TypeMessage -> TypeMessage m
resugarTypeMessage _     M.UnboundVariable      = UnboundVariable
resugarTypeMessage link (M.InvalidInputType  e) =
    InvalidInputType  (resugar link e)
resugarTypeMessage link (M.InvalidOutputType e) =
    InvalidOutputType (resugar link e)
resugarTypeMessage _     M.NotAFunction         = NotAFunction
resugarTypeMessage link (M.TypeMismatch e1 e2 ) =
    TypeMismatch (resugar link e1) (resugar link e2)
resugarTypeMessage _    (M.Untyped c          ) = Untyped c

resugarContext :: (M.Expr -> Maybe m) -> M.Context -> Context m
resugarContext link ctx = Context (do
    (txt, expr) <- ctx
    return (txt, resugar link expr) )

instance Builds TypeError where
    build (TypeError ctx curr msg)
        =   (   if Text.null (toLazyText ctx')
                then mempty
                else "Context:\n" <> ctx' <> "\n"
            )
        <>  "Expression: " <> build curr <> "\n"
        <>  "\n"
        <>  build msg
      where
        ctx' = build ctx

instance Builds TypeMessage where
    build  UnboundVariable           =
            "Error: Unbound variable\n"
    build (InvalidInputType expr)    =
            "Error: Invalid input type\n"
        <>  "\n"
        <>  "Type: " <> build expr <> "\n"
    build (InvalidOutputType expr)   =
            "Error: Invalid output type\n"
        <>  "\n"
        <>  "Type: " <> build expr <> "\n"
    build  NotAFunction              =
            "Error: Only functions may be applied to values\n"
    build (TypeMismatch expr1 expr2) =
            "Error: Function applied to argument of the wrong type\n"
        <>  "\n"
        <>  "Expected type: " <> build expr1 <> "\n"
        <>  "Argument type: " <> build expr2 <> "\n"
    build (Untyped c)                =
            "Error: " <> M.buildConst c <> " has no type\n"

instance Builds Context where
    build
        =   fromLazyText
        .   Text.unlines
        .   map (toLazyText . buildKV)
        .   reverse
        .   getContext
      where
        buildKV (key, val) = fromLazyText key <> " : " <> build val

prettyTypeError :: TypeError FilePath -> Text
prettyTypeError = toLazyText . build
