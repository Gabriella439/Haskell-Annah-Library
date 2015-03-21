{
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Parsing logic for the Annah language

module Annah.Parser (
    -- * Parser
    exprFromText,

    -- * Errors
    prettyParseError,
    ParseError(..),
    ParseMessage(..)
    ) where

import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Error (ErrorT, Error(..), throwError, runErrorT)
import Control.Monad.Trans.State.Strict (State, runState, get, put)
import Data.Functor.Identity (Identity, runIdentity)
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Data.Text.Lazy.IO as Text
import Data.Typeable (Typeable)
import Lens.Family.Stock (_1, _2)
import Lens.Family.State.Strict ((.=), use, zoom)
import Pipes (Producer, hoist, lift, next)

import qualified Annah.Lexer as Lexer
import Annah.Import (Load(..))
import Annah.Lexer (Token, Position)
import Annah.Syntax

}

%name parseExpr
%tokentype { Token }
%monad { Lex }
%lexer { lexer } { Lexer.EOF }
%error { parseError }

%token
    '('     { Lexer.OpenParen  }
    ')'     { Lexer.CloseParen }
    '{'     { Lexer.OpenBrace  }
    '}'     { Lexer.CloseBrace }
    '<'     { Lexer.OpenAngle  }
    '>'     { Lexer.CloseAngle }
    ','     { Lexer.Comma      }
    ':'     { Lexer.Colon      }
    '@'     { Lexer.At         }
    '*'     { Lexer.Star       }
    'BOX'   { Lexer.Box        }
    '->'    { Lexer.Arrow      }
    '\\'    { Lexer.Lambda     }
    '|~|'   { Lexer.Pi         }
    'given' { Lexer.Given      }
    'type'  { Lexer.Type       }
    'fold'  { Lexer.Fold       }
    'data'  { Lexer.Data       }
    'let'   { Lexer.Let        }
    '='     { Lexer.Equals     }
    'in'    { Lexer.In         }
    label   { Lexer.Label $$   }
    number  { Lexer.Number $$  }
    ascii   { Lexer.ASCII $$   }
    file    { Lexer.File $$    }

%%

Expr0 :: { Expr Load }
      : Expr1 ':' Expr0 { Annot $1 $3 }
      | Expr1           { $1          }

Expr1 :: { Expr Load }
      : '\\'  Args                    '->' Expr1      { MultiLam (MultiLambda $2 $4) }
      | '|~|' '(' label ':' Expr1 ')' '->' Expr1      { Pi  $3  $5 $8                }
      | Expr2 '->' Expr1                              { Pi  "_" $1 $3                }
      | Family 'in' Expr1                             { Fam  $1 $3                   }
      | Lets   'in' Expr1                             { Lets $1 $3                   }
      | Expr2                                         { $1                           }

VExpr  :: { Var }
       : label '@' number { V $1 $3 }
       | label            { V $1 0  }

Expr2 :: { Expr Load }
      : Expr2 Expr3 { App $1 $2 }
      | Expr3       { $1        }

Expr3 :: { Expr Load }
      : VExpr                      { Var $1                     }
      | '*'                        { Const Star                 }
      | 'BOX'                      { Const Box                  }
      | file                       { importFile $1              }
      | number                     { Natural (fromIntegral $1)  }
      | ascii                      { ASCII $1                   }
      | '<' ProductValueFields '>' { ProductValue $2            }
      | '{' ProductTypeFields  '}' { ProductType  $2            }
      | '(' Expr0              ')' { $2                         }

Args :: { [Arg Load] }
     : ArgsRev { reverse $1 }

ArgsRev :: { [Arg Load] }
        : ArgsRev Arg { $2 : $1 }
        |             { []      }

Arg :: { Arg Load }
    : '(' label ':' Expr1 ')' { Arg $2  $4 }
    |               Expr3     { Arg "_" $1 }

GivensRev :: { [Arg Load] }
GivensRev : GivensRev 'given' label ':' Expr0 { Arg $3 $5 : $1 }
          |                                   { []             }

Givens :: { [Arg Load] }
Givens : GivensRev { reverse $1 }

Data :: { Data Load }
     : 'data' label Args { Data $2 $3 }

DatasRev :: { [Data Load] }
         : DatasRev Data { $2 : $1 }
         |               { []      }

Datas :: { [Data Load] }
Datas : DatasRev { reverse $1 }

Type :: { Type Load }
Type : 'type' label Datas 'fold' label { Type $2 $5 $3 }

TypesRev :: { [Type Load] }
TypesRev : TypesRev Type { $2 : $1 }
         |               { []      }

Types :: { [Type Load] }
      : TypesRev { reverse $1 }

Family :: { Family m }
Family : Givens Types { Family $1 $2 }

Let :: { Let Load }
    : 'let'  label Args ':' Expr0 '=' Expr1 { Let $2 $3 $5 $7 }

LetsRev :: { [Let Load] }
        : LetsRev Let { $2 : $1 }
        | Let         { [$1]    }

Lets :: { [Let Load] }
     : LetsRev { reverse $1 }

ProductValueField :: { ProductValueSectionField Load }
ProductValueField : Expr1 ':' Expr0 { ValueField (ProductValueField $1 $3) }
                  | Expr0           { TypeValueField $1                    }
                  |                 { EmptyValueField                      }

ProductValueFieldsRev :: { [ProductValueSectionField Load] }
ProductValueFieldsRev : ProductValueFieldsRev ProductValueField ',' { $2 : $1  }
                      |                                             { []       }

ProductValueFields :: { [ProductValueSectionField Load] }
ProductValueFields : ProductValueFieldsRev { reverse $1 }

ProductTypeField :: { ProductTypeSectionField Load }
                 : label ':' Expr0 { TypeField (ProductTypeField $1  $3) }
                 | Expr0           { TypeField (ProductTypeField "_" $1) }
                 |                 { EmptyTypeField                      }

ProductTypeFieldsRev :: { [ProductTypeSectionField Load] }
                     : ProductTypeFieldsRev ProductTypeField ',' { $2 : $1  }
                     |                                           { []       }

ProductTypeFields :: { [ProductTypeSectionField Load] }
ProductTypeFields : ProductTypeFieldsRev { reverse $1 }

{
-- | The specific parsing error
data ParseMessage
    -- | Lexing failed, returning the remainder of the text
    = Lexing Text
    -- | Parsing failed, returning the invalid token
    | Parsing Token
    deriving (Show)

{- This is purely to satisfy the unnecessary `Error` constraint for `ErrorT`

    I will switch to `ExceptT` when the Haskell Platform incorporates
    `transformers-0.4.*`.
-}
instance Error ParseMessage where

type Status = (Position, Producer Token (State Position) (Maybe Text))

type Lex = ErrorT ParseMessage (State Status)

-- To avoid an explicit @mmorph@ dependency
generalize :: Monad m => Identity a -> m a
generalize = return . runIdentity

lexer :: (Token -> Lex a) -> Lex a
lexer k = do
    x <- lift (do
        p <- use _2
        hoist generalize (zoom _1 (next p)) )
    case x of
        Left ml           -> case ml of
            Nothing -> k Lexer.EOF
            Just le -> throwError (Lexing le)
        Right (token, p') -> do
            lift (_2 .= p')
            k token

parseError :: Token -> Lex a
parseError token = throwError (Parsing token)

-- | Parse an `Expr` from `Text` or return a `ParseError` if parsing fails
exprFromText :: Text -> Either ParseError (Expr Load)
exprFromText text = case runState (runErrorT parseExpr) initialStatus of
    (x, (position, _)) -> case x of
        Left  e    -> Left (ParseError position e)
        Right expr -> Right expr
  where
    initialStatus = (Lexer.P 1 0, Lexer.lexExpr text)

-- | Structured type for parsing errors
data ParseError = ParseError
    { position     :: Position
    , parseMessage :: ParseMessage
    } deriving (Typeable)

instance Show ParseError where
    show = unpack . prettyParseError

instance Exception ParseError

-- | Pretty-print a `ParseError`
prettyParseError :: ParseError -> Text
prettyParseError (ParseError (Lexer.P l c) e) = Builder.toLazyText (
        "\n"
    <>  "Line:   " <> decimal l <> "\n"
    <>  "Column: " <> decimal c <> "\n"
    <>  "\n"
    <>  case e of
        Lexing r  ->
                "Lexing: \"" <> Builder.fromLazyText remainder <> dots <> "\"\n"
            <>  "\n"
            <>  "Error: Lexing failed\n"
          where
            remainder = Text.takeWhile (/= '\n') (Text.take 64 r)
            dots      = if Text.length r > 64 then "..." else mempty
        Parsing t ->
                "Parsing: " <> Builder.fromString (show t) <> "\n"
            <>  "\n"
            <>  "Error: Parsing failed\n" )

-- TODO: Check for normalized or serialized alternatives when importing
--       expressions
importFile :: Text -> Expr Load
importFile path = Import (Load (do
    m <- get
    case HashMap.lookup path m of
        Just expr -> return expr
        Nothing   -> do
            txt <- liftIO (Text.readFile (unpack path))
            case exprFromText txt of
                Left pe    -> liftIO (throwIO pe)
                Right expr -> do
                    put (HashMap.insert path expr m)
                    return expr ))
}
