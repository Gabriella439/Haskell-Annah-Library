{
{-# LANGUAGE OverloadedStrings #-}

-- | Lexing logic for the Annah language
module Annah.Lexer (
    -- * Lexer
    lexExpr,

    -- * Types
    Token(..),
    Position(..)
    ) where

import Control.Monad.Trans.State.Strict (State)
import Data.Bits (shiftR, (.&.))
import Data.Char (ord, digitToInt, isDigit)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Data.Word (Word8)
import Filesystem.Path.CurrentOS (FilePath, fromText)
import Lens.Family.State.Strict ((.=), (+=))
import Pipes (Producer, lift, yield)
import Prelude hiding (FilePath)

}

$digit = 0-9

-- Same as Haskell
$opchar = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]

$fst   = [A-Za-z_]
$label = [A-Za-z0-9_]
$ascii = [\x00-\x7f] # [\x22]

$nonwhite       = ~$white
$whiteNoNewline = $white # \n

$path = [$label \\\/\.]

tokens :-

    $whiteNoNewline+                  ;
    \n                              { \_    -> lift (do
                                        line   += 1
                                        column .= 0 )                          }
    "--".*                          ;
    "("                             { \_    -> yield OpenParen                 }
    ")"                             { \_    -> yield CloseParen                }
    "{"                             { \_    -> yield OpenBrace                 }
    "}"                             { \_    -> yield CloseBrace                }
    "[nil"                          { \_    -> yield OpenList                  }
    "[id"                           { \_    -> yield OpenPath                  }
    "]"                             { \_    -> yield CloseBracket              }
    \" $ascii* \"                   { \text -> yield (String (trim text))      }
    ","                             { \_    -> yield Comma                     }
    ":"                             { \_    -> yield Colon                     }
    ";"                             { \_    -> yield Semicolon                 }
    "@"                             { \_    -> yield At                        }
    "*"                             { \_    -> yield Star                      }
    "BOX" | "□"                     { \_    -> yield Box                       }
    "->" | "→"                      { \_    -> yield Arrow                     }
    "<-" | "←"                      { \_    -> yield LArrow                    }
    "\/" | "|~|" | "forall" | "∀" | "Π" { \_ -> yield Pi                       }
    "\" | "λ"                       { \_    -> yield Lambda                    }
    "type"                          { \_    -> yield Type                      }
    "fold"                          { \_    -> yield Fold                      }
    "data"                          { \_    -> yield Data                      }
    "let"                           { \_    -> yield Let                       }
    "="                             { \_    -> yield Equals                    }
    "in"                            { \_    -> yield In                        }
    "do"                            { \_    -> yield Do                        }
    $digit+                         { \text -> yield (Number (toInt text))     }
    $fst $label* | "(" $opchar+ ")" { \text -> yield (Label text)              }
    "#https://" $nonwhite+          { \text -> yield (URL (toUrl text))        }
    "#http://" $nonwhite+           { \text -> yield (URL (toUrl text))        }
    "#" $nonwhite+                  { \text -> yield (File (toFile text))      }

{
toInt :: Text -> Int
toInt = Text.foldl' (\x c -> 10 * x + digitToInt c) 0

toUrl :: Text -> Text
toUrl = Text.drop 1

toFile :: Text -> FilePath
toFile = fromText . Text.toStrict . Text.drop 1

trim :: Text -> Text
trim = Text.init . Text.tail

-- This was lifted almost intact from the @alex@ source code
encode :: Char -> (Word8, [Word8])
encode c = (fromIntegral h, map fromIntegral t)
  where
    (h, t) = go (ord c)

    go n
        | n <= 0x7f   = (n, [])
        | n <= 0x7ff  = (0xc0 + (n `shiftR` 6), [0x80 + n .&. 0x3f])
        | n <= 0xffff =
            (   0xe0 + (n `shiftR` 12)
            ,   [   0x80 + ((n `shiftR` 6) .&. 0x3f)
                ,   0x80 + n .&. 0x3f
                ]
            )
        | otherwise   =
            (   0xf0 + (n `shiftR` 18)
            ,   [   0x80 + ((n `shiftR` 12) .&. 0x3f)
                ,   0x80 + ((n `shiftR` 6) .&. 0x3f)
                ,   0x80 + n .&. 0x3f
                ]
            )

-- | The cursor's location while lexing the text
data Position = P
    { lineNo    :: {-# UNPACK #-} !Int
    , columnNo  :: {-# UNPACK #-} !Int
    } deriving (Show)

-- line :: Lens' Position Int
line :: Functor f => (Int -> f Int) -> Position -> f Position
line k (P l c) = fmap (\l' -> P l' c) (k l)

-- column :: Lens' Position Int
column :: Functor f => (Int -> f Int) -> Position -> f Position
column k (P l c) = fmap (\c' -> P l c') (k c)

{- @alex@ does not provide a `Text` wrapper, so the following code just modifies
   the code from their @basic@ wrapper to work with `Text`

   I could not get the @basic-bytestring@ wrapper to work; it does not correctly
   recognize Unicode regular expressions.
-}
data AlexInput = AlexInput
    { prevChar  :: Char
    , currBytes :: [Word8]
    , currInput :: Text
    }

alexGetByte :: AlexInput -> Maybe (Word8,AlexInput)
alexGetByte (AlexInput c bytes text) = case bytes of
    b:ytes -> Just (b, AlexInput c ytes text)
    []     -> case Text.uncons text of
        Nothing       -> Nothing
        Just (t, ext) -> case encode t of
            (b, ytes) -> Just (b, AlexInput t ytes ext)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = prevChar

{-| Convert a text representation of an expression into a stream of tokens

    `lexExpr` keeps track of position and returns the remainder of the input if
    lexing fails.
-}
lexExpr :: Text -> Producer Token (State Position) (Maybe Text)
lexExpr text = go (AlexInput '\n' [] text)
  where
    go input = case alexScan input 0 of
        AlexEOF                        -> return Nothing
        AlexError (AlexInput _ _ text) -> return (Just text)
        AlexSkip  input' len           -> do
            lift (column += len)
            go input'
        AlexToken input' len act       -> do
            act (Text.take (fromIntegral len) (currInput input))
            lift (column += len)
            go input'

-- | Token type, used to communicate between the lexer and parser
data Token
    = OpenParen
    | CloseParen
    | OpenBrace
    | CloseBrace
    | OpenList
    | OpenPath
    | CloseBracket
    | String Text
    | Period
    | Comma
    | Colon
    | Semicolon
    | At
    | Star
    | Box
    | Arrow
    | LArrow
    | Lambda
    | Pi
    | Type
    | Fold
    | Data
    | Let
    | Equals
    | In
    | Do
    | Label Text
    | Number Int
    | File FilePath
    | URL Text
    | EOF
    deriving (Show)
}
