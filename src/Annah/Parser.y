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
import Data.Monoid (mempty, (<>))
import Data.Text.Lazy (Text, unpack)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import Data.Text.Lazy.Builder.Int (decimal)
import qualified Data.Text.Lazy.IO as Text
import Data.Typeable (Typeable)
import Lens.Family.Stock (_1, _2)
import Lens.Family.State.Strict ((.=), use, zoom)
import Morte.Core (Path(..))
import Pipes (Producer, hoist, lift, next)

import qualified Annah.Lexer as Lexer
import Annah.Lexer (Token, Position)
import Annah.Core

}

%name parseExpr
%tokentype { Token }
%monad { Lex }
%lexer { lexer } { Lexer.EOF }
%error { parseError }

%token
    '('     { Lexer.OpenParen        }
    ')'     { Lexer.CloseParen       }
    '{'     { Lexer.OpenBrace        }
    '}'     { Lexer.CloseBrace       }
    '[nil'  { Lexer.OpenList         }
    '[id'   { Lexer.OpenPath         }
    ']'     { Lexer.CloseBracket     }
    '.'     { Lexer.Period           }
    ','     { Lexer.Comma            }
    ':'     { Lexer.Colon            }
    ';'     { Lexer.Semicolon        }
    '@'     { Lexer.At               }
    '*'     { Lexer.Star             }
    'BOX'   { Lexer.Box              }
    '->'    { Lexer.Arrow            }
    '<-'    { Lexer.LArrow           }
    '\\'    { Lexer.Lambda           }
    '|~|'   { Lexer.Pi               }
    'type'  { Lexer.Type             }
    'fold'  { Lexer.Fold             }
    'data'  { Lexer.Data             }
    'let'   { Lexer.Let              }
    '='     { Lexer.Equals           }
    'in'    { Lexer.In               }
    'do'    { Lexer.Do               }
    label   { Lexer.Label $$         }
    number  { Lexer.Number $$        }
    string  { Lexer.String $$        }
    file    { Lexer.File $$          }
    url     { Lexer.URL $$           }

%%

Expr0 :: { Expr }
    : Expr1 ':' Expr0 { Annot $1 $3 }
    | Expr1           { $1          }

Expr1 :: { Expr }
    : '\\'  '(' label ':' Expr1 ')' '->' Expr1 { Lam $3  $5 $8 }
    | '|~|' '(' label ':' Expr1 ')' '->' Expr1 { Pi  $3  $5 $8 }
    | Expr2 '->' Expr1                         { Pi  "_" $1 $3 }
    | Types 'in' Expr1                         { Family  $1 $3 }
    | Lets  'in' Expr1                         { Lets $1 $3    }
    | Expr2                                    { $1            }

VExpr  :: { Var }
    : label '@' number { V $1 $3 }
    | label            { V $1 0  }

Expr2 :: { Expr }
    : Expr2 Expr3 { App $1 $2 }
    | Expr3       { $1        }

Expr3 :: { Expr }
    : VExpr                       { Var $1                                   }
    | '*'                         { Const Star                               }
    | 'BOX'                       { Const Box                                }
    | Embed                       { Embed $1                                 }
    | number                      { Natural (fromIntegral $1)                }
    | string                      { String $1                                }
    | '[nil' Expr0 ListFields ']' { List $2 $3                               }
    | '[id'  Expr0 PathFields ']' { let ~(oms, o) = $3 in Path $2 oms o      }
    | 'do' Expr0 '{' Binds '}'    { let (init, last) = $4 in Do $2 init last }
    | '(' Expr0               ')' { $2                                       }

Args :: { [Arg] }
    : ArgsRev { reverse $1 }

ArgsRev :: { [Arg] }
    : ArgsRev Arg { $2 : $1 }
    |             { []      }

Arg :: { Arg }
    : '(' label ':' Expr1 ')' { Arg $2  $4 }
    |               Expr3     { Arg "_" $1 }

Data :: { Data }
    : 'data' label Args { Data $2 $3 }

DatasRev :: { [Data] }
    : DatasRev Data { $2 : $1 }
    |               { []      }

Datas :: { [Data] }
    : DatasRev { reverse $1 }

Type :: { Type }
    : 'type' label Datas 'fold' label { Type $2 $3 $5  }
    | 'type' label Datas              { Type $2 $3 "_" }

TypesRev :: { [Type] }
    : TypesRev Type { $2 : $1 }
    |               { []      }

Types :: { [Type] }
    : TypesRev { reverse $1 }

Let :: { Let }
    : 'let'  label Args ':' Expr0 '=' Expr1 { Let $2 $3 $5 $7 }

LetsRev :: { [Let] }
    : LetsRev Let { $2 : $1 }
    | Let         { [$1]    }

Lets :: { [Let] }
    : LetsRev { reverse $1 }

ListFields :: { [Expr] }
    : ListFieldsRev { reverse $1 }

ListFieldsRev :: { [Expr] }
    : ListFieldsRev ',' Expr0 { $3 : $1 }
    |                         { []      }

PathFields :: { ([(Expr, Expr)], Expr) }
    : Object Expr0 PathFields { let ~(oms, o) = $3 in (($1, $2):oms, o) }
    | Object                  { ([], $1)                                }

Object :: { Expr }
    : '{' Expr0 '}' { $2 }

Bind :: { Bind }
    : label ':' Expr0 '<-' Expr0 ';' { Bind (Arg $1 $3) $5 }

Binds :: { ([Bind], Bind) }
    : Bind Binds { let ~(init, last) = $2 in ($1:init, last) }
    | Bind       { ([], $1)                                  }

Embed :: { Path }
    : file { File $1 }
    | url  { URL  $1 }

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
exprFromText :: Text -> Either ParseError Expr
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
}
