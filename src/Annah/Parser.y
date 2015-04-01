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
import Pipes (Producer, hoist, lift, next)
import Turtle (FilePath, fromText)
import Prelude hiding (FilePath)

import qualified Annah.Lexer as Lexer
import Annah.Lexer (Token, Position)
import Annah.Syntax

}

%name parseExpr
%tokentype { Token }
%monad { Lex }
%lexer { lexer } { Lexer.EOF }
%error { parseError }

%token
    '(|'    { Lexer.OpenBanana        }
    '|)'    { Lexer.CloseBanana       }
    '('     { Lexer.OpenParen         }
    ')'     { Lexer.CloseParen        }
    '[*'    { Lexer.OpenList          }
    '[.'    { Lexer.OpenPath          }
    ']'     { Lexer.CloseBracket      }
    '{1'    { Lexer.OpenProductType   }
    '{0'    { Lexer.OpenSumType       }
    '}'     { Lexer.CloseBrace        }
    '<1'    { Lexer.OpenProductValue  }
    '>'     { Lexer.CloseAngle        }
    '.'     { Lexer.Period            }
    ','     { Lexer.Comma             }
    '|'     { Lexer.Bar               }
    ':'     { Lexer.Colon             }
    '@'     { Lexer.At                }
    '*'     { Lexer.Star              }
    'BOX'   { Lexer.Box               }
    '->'    { Lexer.Arrow             }
    '\\'    { Lexer.Lambda            }
    '|~|'   { Lexer.Pi                }
    'given' { Lexer.Given             }
    'type'  { Lexer.Type              }
    'fold'  { Lexer.Fold              }
    'data'  { Lexer.Data              }
    'let'   { Lexer.Let               }
    '='     { Lexer.Equals            }
    'in'    { Lexer.In                }
    of      { Lexer.Of $$             }
    label   { Lexer.Label $$          }
    number  { Lexer.Number $$         }
    ascii   { Lexer.ASCII $$          }
    file    { Lexer.File $$           }

%%

Expr0 :: { Expr FilePath }
    : Expr1 ':' Expr0 { Annot $1 $3 }
    | Expr1           { $1          }

Expr1 :: { Expr FilePath }
    : '\\'  '(' label ':' Expr1 ')' '->' Expr1 { Lam $3  $5 $8 }
    | '|~|' '(' label ':' Expr1 ')' '->' Expr1 { Pi  $3  $5 $8 }
    | Expr2 '->' Expr1                         { Pi  "_" $1 $3 }
    | Family 'in' Expr1                        { Fam  $1 $3    }
    | Lets   'in' Expr1                        { Lets $1 $3    }
    | Expr2                                    { $1            }

VExpr  :: { Var }
    : label '@' number { V $1 $3 }
    | label            { V $1 0  }

Expr2 :: { Expr FilePath }
    : Expr2 Expr3 { App $1 $2 }
    | Expr3       { $1        }

Expr3 :: { Expr FilePath }
    : VExpr                       { Var $1                               }
    | '*'                         { Const Star                           }
    | 'BOX'                       { Const Box                            }
    | file                        { Import (fromText (Text.toStrict $1)) }
    | of                          { uncurry SumConstructor $1            }
    | number                      { Natural (fromIntegral $1)            }
    | ascii                       { ASCII $1                             }
    | '<1' ProductValueFields '>' { ProductValue $2                      }
    | '{1' ProductTypeFields  '}' { ProductType  $2                      }
    | '{0' SumTypeFields      '}' { SumType      $2                      }
    | '[*' Expr0 ListFields   ']' { List $2 $3                           }
    | '[.' Expr0 PathFields   ']' { let ~(oms, o) = $3 in Path $2 oms o  }
    | '(' Expr0               ')' { $2                                   }

Args :: { [Arg FilePath] }
     : ArgsRev { reverse $1 }

ArgsRev :: { [Arg FilePath] }
    : ArgsRev Arg { $2 : $1 }
    |             { []      }

Arg :: { Arg FilePath }
    : '(' label ':' Expr1 ')' { Arg $2  $4 }
    |               Expr3     { Arg "_" $1 }

GivensRev :: { [Arg FilePath] }
    : GivensRev 'given' label ':' Expr0 { Arg $3 $5 : $1 }
    |                                   { []             }

Givens :: { [Arg FilePath] }
    : GivensRev { reverse $1 }

Data :: { Data FilePath }
    : 'data' label Args { Data $2 $3 }

DatasRev :: { [Data FilePath] }
    : DatasRev Data { $2 : $1 }
    |               { []      }

Datas :: { [Data FilePath] }
    : DatasRev { reverse $1 }

Type :: { Type FilePath }
    : 'type' label Datas 'fold' label { Type $2 $5 $3 }

TypesRev :: { [Type FilePath] }
    : TypesRev Type { $2 : $1 }
    |               { []      }

Types :: { [Type FilePath] }
    : TypesRev { reverse $1 }

Family :: { Family m }
    : Givens Types { Family $1 $2 }

Let :: { Let FilePath }
    : 'let'  label Args ':' Expr0 '=' Expr1 { Let $2 $3 $5 $7 }

LetsRev :: { [Let FilePath] }
    : LetsRev Let { $2 : $1 }
    | Let         { [$1]    }

Lets :: { [Let FilePath] }
    : LetsRev { reverse $1 }

ProductValueField :: { ProductValueSectionField FilePath }
    : Expr1 ':' Expr0 { ValueField (ProductValueField $1 $3) }
    | Expr0           { TypeValueField $1                    }
    |                 { EmptyValueField                      }

ProductValueFieldsRev :: { [ProductValueSectionField FilePath] }
    : ProductValueFieldsRev ',' ProductValueField { $3 : $1  }
    |                                             { []       }

ProductValueFields :: { [ProductValueSectionField FilePath] }
    : ProductValueFieldsRev { reverse $1 }

ProductTypeField :: { ProductTypeSectionField FilePath }
    : label ':' Expr0 { TypeField (ProductTypeField $1  $3) }
    | Expr0           { TypeField (ProductTypeField "_" $1) }
    |                 { EmptyTypeField                      }

ProductTypeFieldsRev :: { [ProductTypeSectionField FilePath] }
    : ProductTypeFieldsRev ',' ProductTypeField { $3 : $1  }
    |                                           { []       }

ProductTypeFields :: { [ProductTypeSectionField FilePath] }
    : ProductTypeFieldsRev { reverse $1 }

SumTypeFieldsRev :: { [SumTypeSectionField FilePath] }
    : SumTypeFieldsRev '|' SumTypeSectionField { $3 : $1 }
    |                                          { []      }

SumTypeFields :: { [SumTypeSectionField FilePath] }
    : SumTypeFieldsRev { reverse $1 }

SumTypeSectionField :: { SumTypeSectionField FilePath }
    : Expr0 { SumTypeField $1   }
    |       { EmptySumTypeField }

ListFields :: { [Expr FilePath] }
    : ListFieldsRev { reverse $1 }

ListFieldsRev :: { [Expr FilePath] }
    : ListFieldsRev ',' Expr0 { $3 : $1 }
    |                         { []      }

PathFields :: { ([(Expr FilePath, Expr FilePath)], Expr FilePath) }
    : Object Expr0 PathFields { let ~(oms, o) = $3 in (($1, $2):oms, o) }
    | Object                  { ([], $1)                                }

Object :: { Expr FilePath }
    : '(|' Expr0 '|)' { $2 }

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
exprFromText :: Text -> Either ParseError (Expr FilePath)
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
