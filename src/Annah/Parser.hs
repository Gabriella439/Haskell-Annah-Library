{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecursiveDo        #-}

-- | Parsing logic for the Morte language

module Annah.Parser (
    -- * Parser
    exprFromText,
    typesFromText,

    -- * Errors
    ParseError(..),
    ParseMessage(..)
    ) where

import Annah.Core
import Annah.Lexer (Position, Token, LocatedToken(..))
import Control.Applicative hiding (Const)
import Control.Exception (Exception)
import Control.Monad.Trans.Class  (lift)
import Control.Monad.Trans.Except (Except, throwE, runExceptT)
import Control.Monad.Trans.State.Strict (evalState, get)
import Data.Monoid
import Data.Text.Buildable (Buildable(..))
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (toLazyText)
import Data.Typeable (Typeable)
import Morte.Core (Path(..))
import Filesystem.Path.CurrentOS (FilePath)
import Prelude hiding (FilePath)
import Text.Earley

import qualified Annah.Lexer    as Lexer
import qualified Pipes.Prelude  as Pipes
import qualified Data.Text.Lazy as Text

match :: Token -> Prod r Token LocatedToken Token
match t = fmap Lexer.token (satisfy predicate) <?> t
  where
    predicate (LocatedToken t' _) = t == t'

label :: Prod r e LocatedToken Text
label = fmap unsafeFromLabel (satisfy isLabel)
  where
    isLabel (LocatedToken (Lexer.Label _) _) = True
    isLabel  _                               = False

    unsafeFromLabel (LocatedToken (Lexer.Label l) _) = l

number :: Prod r e LocatedToken Int
number = fmap unsafeFromNumber (satisfy isNumber)
  where
    isNumber (LocatedToken (Lexer.Number _) _) = True
    isNumber  _                                = False

    unsafeFromNumber (LocatedToken (Lexer.Number n) _) = n

file :: Prod r e LocatedToken FilePath
file = fmap unsafeFromFile (satisfy isFile)
  where
    isFile (LocatedToken (Lexer.File _) _) = True
    isFile  _                              = False

    unsafeFromFile (LocatedToken (Lexer.File n) _) = n

url :: Prod r e LocatedToken Text
url = fmap unsafeFromURL (satisfy isURL)
  where
    isURL (LocatedToken (Lexer.URL _) _) = True
    isURL  _                             = False

    unsafeFromURL (LocatedToken (Lexer.URL n) _) = n

sepBy1 :: Alternative f => f a -> f b -> f [a]
sepBy1 x sep = (:) <$> x <*> many (sep *> x)

sepBy :: Alternative f => f a -> f b -> f [a]
sepBy x sep = sepBy1 x sep <|> pure []

expr
    :: Grammar r
        (Prod r Token LocatedToken Expr, Prod r Token LocatedToken [Type])
expr = mdo
    expr0 <- rule
        (   Annot <$> expr1 <*> (match Lexer.Colon *> expr0)
        <|> expr1
        )
    expr1 <- rule
        (       Lam
            <$> (match Lexer.Lambda *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr1)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr1)
        <|>     Pi
            <$> (match Lexer.Pi *> match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr1)
            <*> (match Lexer.CloseParen *> match Lexer.Arrow *> expr1)
        <|> Pi "_" <$> expr2 <*> (match Lexer.Arrow *> expr1)
        <|> Family <$> types <*> (match Lexer.In *> expr1)
        <|> Lets <$> lets <*> (match Lexer.In *> expr1)
        <|> expr2
        )

    vexpr <- rule
        (   V <$> label <*> (match Lexer.At *> number)
        <|> V <$> label <*> pure 0
        )

    expr2 <- rule
        (   App <$> expr2 <*> expr3
        <|> expr3
        )

    let makeExpr3 p =
            (   Var <$> vexpr
            <|> match Lexer.Star *> pure (Const Star)
            <|> match Lexer.Box  *> pure (Const Box )
            <|> Embed <$> embed
            <|> (Natural . fromIntegral) <$> number
            <|>     List
                <$> (match Lexer.OpenList *> expr0)
                <*> (many (match Lexer.Comma *> expr0) <* match Lexer.CloseBracket)
            <|>     Path
                <$> (match Lexer.OpenPath *> expr0)
                <*> many ((,) <$> object <*> expr0)
                <*> (object <* match Lexer.CloseBracket)
            <|>     Do
                <$> (match Lexer.Do *> expr0)
                <*> (match Lexer.OpenBrace *> many bind)
                <*> (bind <* match Lexer.CloseBrace)
            <|> (match Lexer.OpenParen *> p <* match Lexer.CloseParen)
            )

    expr3  <- rule (makeExpr3 expr0)
    expr3' <- rule (makeExpr3 expr1)

    arg <- rule
        (       Arg
            <$> (match Lexer.OpenParen *> label)
            <*> (match Lexer.Colon *> expr1 <* match Lexer.CloseParen)
        <|>     Arg "_" <$> expr3'
        )

    args <- rule (many arg)

    data_ <- rule (Data <$> (match Lexer.Data *> label) <*> args)

    datas <- rule (many data_)

    type_ <- rule
        (       Type
            <$> (match Lexer.Type *> label)
            <*> datas
            <*> (match Lexer.Fold *> label)
        <|>     Type
            <$> (match Lexer.Type *> label)
            <*> datas
            <*> pure "_"
        )

    types <- rule (some type_)

    let_ <- rule
        (   Let
        <$> (match Lexer.Let *> label)
        <*> args
        <*> (match Lexer.Colon *> expr0)
        <*> (match Lexer.Equals *> expr1)
        )

    lets <- rule (some let_)

    object <- rule (match Lexer.OpenBrace *> expr0 <* match Lexer.CloseBrace)

    bind <- rule
        (   (\x y z -> Bind (Arg x y) z)
        <$> label
        <*> (match Lexer.Colon *> expr0)
        <*> (match Lexer.LArrow *> expr0 <* match Lexer.Semicolon)
        )

    embed <- rule
        (   File <$> file
        <|> URL <$> url
        )

    return (expr0, types)

-- | The specific parsing error
data ParseMessage
    -- | Lexing failed, returning the remainder of the text
    = Lexing Text
    -- | Parsing failed, returning the invalid token and the expected tokens
    | Parsing Token [Token]
    deriving (Show)

-- | Structured type for parsing errors
data ParseError = ParseError
    { position     :: Position
    , parseMessage :: ParseMessage
    } deriving (Typeable)

instance Show ParseError where
    show = Text.unpack . toLazyText . build

instance Exception ParseError

instance Buildable ParseError where
    build (ParseError (Lexer.P l c) e) =
            "\n"
        <>  "Line:   " <> build l <> "\n"
        <>  "Column: " <> build c <> "\n"
        <>  "\n"
        <>  case e of
            Lexing r                                     ->
                    "Lexing: \"" <> build remainder <> dots <> "\"\n"
                <>  "\n"
                <>  "Error: Lexing failed\n"
              where
                remainder = Text.takeWhile (/= '\n') (Text.take 64 r)
                dots      = if Text.length r > 64 then "..." else mempty
            Parsing t ts ->
                    "Parsing : " <> build (show t ) <> "\n"
                <>  "Expected: " <> build (show ts) <> "\n"
                <>  "\n"
                <>  "Error: Parsing failed\n"

runParser
    :: (forall r . Grammar r (Prod r Token LocatedToken a))
    -> Text
    -> Either ParseError a
runParser p text = evalState (runExceptT m) (Lexer.P 1 0)
  where
    m = do
        (locatedTokens, mtxt) <- lift (Pipes.toListM' (Lexer.lexExpr text))
        case mtxt of
            Nothing  -> return ()
            Just txt -> do
                pos <- lift get
                throwE (ParseError pos (Lexing txt))
        let (parses, Report _ needed found) =
                fullParses (parser p) locatedTokens
        case parses of
            parse:_ -> return parse
            []      -> do
                let LocatedToken t pos = case found of
                        lt:_ -> lt
                        _    -> LocatedToken Lexer.EOF (Lexer.P 0 0)
                throwE (ParseError pos (Parsing t needed))

-- | Parse an `Expr` from `Text` or return a `ParseError` if parsing fails
exprFromText :: Text -> Either ParseError Expr
exprFromText = runParser (fmap fst expr)

{-| Parse a type definition from `Text` or return a `ParseError` if parsing
    fails
-}
typesFromText :: Text -> Either ParseError [Type]
typesFromText = runParser (fmap snd expr)
