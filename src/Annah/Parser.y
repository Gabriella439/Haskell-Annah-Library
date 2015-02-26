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
import Control.Monad.Trans.Error (ErrorT, Error(..), throwError, runErrorT)
import Control.Monad.Trans.State.Strict (State, runState)
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

import Annah.Core
import qualified Annah.Lexer as Lexer
import Annah.Lexer (Token, Position)

}

%name parseExpr
%tokentype { Token }
%monad { Lex }
%lexer { lexer } { Lexer.EOF }
%error { parseError }

%token
    '('     { Lexer.OpenParen  }
    ')'     { Lexer.CloseParen }
    ':'     { Lexer.Colon      }
    '@'     { Lexer.At         }
    '*'     { Lexer.Star       }
    'BOX'   { Lexer.Box        }
    '->'    { Lexer.Arrow      }
    '\\'    { Lexer.Lambda     }
    '|~|'   { Lexer.Pi         }
    'type'  { Lexer.Type       }
    'data'  { Lexer.Data       }
    'fold'  { Lexer.Fold       }
    'let'   { Lexer.Let        }
    '='     { Lexer.Equals     }
    'in'    { Lexer.In         }
    label   { Lexer.Label $$   }
    number  { Lexer.Number $$  }
    file    { Lexer.File $$    }

%%

Expr0 :: { Expr IO }
      : Expr1 ':' Expr0 { Annot $1 $3 }
      | Expr1           { $1          }

Decl :: { Decl IO }
     : label Args ':' Expr0 { Decl $1 $2 $4 }

Stmt :: { Stmt IO }
Stmt : 'type' Decl           { Stmt $2  Type    }
     | 'data' Decl           { Stmt $2  Data    }
     | 'fold' Decl           { Stmt $2  Fold    }
     | 'let'  Decl '=' Expr1 { Stmt $2 (Let $4) }

StmtsRev :: { [Stmt IO] }
         : StmtsRev Stmt { $2 : $1 }
         | Stmt         { [$1] }

Stmts :: { [Stmt IO] }
Stmts : StmtsRev { reverse $1 }

Expr1 :: { Expr IO }
      : '\\'  '(' label ':' Expr1 ')' '->' Expr1      { Lam $3 $5 $8 }
      | '|~|' '(' label ':' Expr1 ')' '->' Expr1      { Pi  $3 $5 $8 }
      | Expr2 '->' Expr1                              { Pi "_" $1 $3 }
      | Stmts 'in' Expr1                              { Stmts $1 $3  }
      | Expr2                                         { $1           }

Args :: { [Arg IO] }
     : ArgsRev { reverse $1 }

ArgsRev :: { [Arg IO] }
        : ArgsRev Arg { $2 : $1 }
        |             { []      }

Arg :: { Arg IO }
    : '(' label ':' Expr0 ')' { Arg $2 $4 }

VExpr  :: { Var }
       : label '@' number { V $1 $3 }
       | label            { V $1 0  }

Expr2 :: { Expr IO }
      : Expr2 Expr3 { App $1 $2 }
      | Expr3       { $1        }

Expr3 :: { Expr IO }
      : VExpr         { Var $1        }
      | '*'           { Const Star    }
      | 'BOX'         { Const Box     }
      | file          { importFile $1 }
      | '(' Expr0 ')' { $2            }

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
exprFromText :: Text -> Either ParseError (Expr IO)
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
        "Line:   " <> decimal l <> "\n"
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

importFile :: Text -> Expr IO
importFile path = Import (do
    txt <- Text.readFile (unpack path)
    case exprFromText txt of
        Left pe    -> throwIO pe
        Right expr -> return expr )
}
