{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wall #-}

module Annah.Error (
    -- * Error
      TypeError(..)
    , TypeMessage(..)
    , Context
    , resugarTypeError
    ) where

import Control.Exception (Exception)
import Data.Monoid (mempty, (<>))
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (toLazyText)
import Data.Typeable (Typeable)
import qualified Morte.Core as M

import Annah.Sugar (resugar)
import Annah.Syntax (Expr)

data TypeError = TypeError
    { context     :: Context
    , current     :: Expr M.X
    , typeMessage :: TypeMessage
    } deriving (Typeable)

instance Show TypeError where
    show = unpack . toLazyText. build

instance Exception TypeError

data TypeMessage
    = UnboundVariable
    | InvalidInputType (Expr M.X)
    | InvalidOutputType (Expr M.X)
    | NotAFunction
    | TypeMismatch (Expr M.X) (Expr M.X)
    | Untyped M.Const

newtype Context = Context { getContext :: [(Text, Expr M.X)] }

instance Show TypeMessage where
    show = unpack . toLazyText . build

resugarTypeError :: M.TypeError -> TypeError
resugarTypeError (M.TypeError ctx curr msg) = TypeError
    (resugarContext ctx)
    (resugar curr)
    (resugarTypeMessage msg)

resugarTypeMessage :: M.TypeMessage -> TypeMessage
resugarTypeMessage  M.UnboundVariable      = UnboundVariable
resugarTypeMessage (M.InvalidInputType  e) =
    InvalidInputType  (resugar e)
resugarTypeMessage (M.InvalidOutputType e) =
    InvalidOutputType (resugar e)
resugarTypeMessage  M.NotAFunction         = NotAFunction
resugarTypeMessage (M.TypeMismatch e1 e2 ) =
    TypeMismatch (resugar e1) (resugar e2)
resugarTypeMessage (M.Untyped c          ) = Untyped c

resugarContext :: M.Context -> Context
resugarContext ctx = Context (do
    (txt, expr) <- ctx
    return (txt, resugar expr) )

instance Buildable TypeError where
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

instance Buildable TypeMessage where
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
            "Error: " <> build c <> " has no type\n"

instance Buildable Context where
    build
        =   build
        .   Text.unlines
        .   map (toLazyText . buildKV)
        .   reverse
        .   getContext
      where
        buildKV (key, val) = build key <> " : " <> build val
