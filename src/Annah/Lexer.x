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
import Lens.Family.State.Strict ((.=), (+=))
import Pipes (Producer, lift, yield)

}

$digit = 0-9

-- Same as Haskell
$opchar = [\!\#\$\%\&\*\+\.\/\<\=\>\?\@\\\^\|\-\~]

$fst   = [A-Za-z_]
$label = [A-Za-z0-9_]
$ascii = [\x00-\x7f] # [\x22]

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
    "["                             { \_    -> yield OpenBracket               }
    "]"                             { \_    -> yield CloseBracket              }
    "{1"                            { \_    -> yield OpenProductType           }
    "{0"                            { \_    -> yield OpenSumType               }
    "}"                             { \_    -> yield CloseBrace                }
    "<1"                            { \_    -> yield OpenProductValue          }
    ">"                             { \_    -> yield CloseAngle                }
    \" $ascii* \"                   { \text -> yield (ASCII (trim text))       }
    ","                             { \_    -> yield Comma                     }
    "|"                             { \_    -> yield Bar                       }
    ":"                             { \_    -> yield Colon                     }
    "#" $path* "(" $opchar+ ")"     { \text -> yield (File (Text.drop 1 text)) }
    "#" $path+                      { \text -> yield (File (Text.drop 1 text)) }
    "@"                             { \_    -> yield At                        }
    "*"                             { \_    -> yield Star                      }
    "BOX" | "□"                     { \_    -> yield Box                       }
    "->" | "→"                      { \_    -> yield Arrow                     }
    "\/" | "|~|" | "forall" | "∀" | "Π" { \_ -> yield Pi                       }
    "\" | "λ"                       { \_    -> yield Lambda                    }
    "given"                         { \_    -> yield Given                     }
    "type"                          { \_    -> yield Type                      }
    "fold"                          { \_    -> yield Fold                      }
    "data"                          { \_    -> yield Data                      }
    "let"                           { \_    -> yield Let                       }
    "="                             { \_    -> yield Equals                    }
    "in"                            { \_    -> yield In                        }
    $digit+ "to" $digit+            { \txt  -> yield (parseOf txt)             }
    $digit+                         { \text -> yield (Number (toInt text))     }
    $fst $label* | "(" $opchar+ ")" { \text -> yield (Label text)              }

{
toInt :: Text -> Int
toInt = Text.foldl' (\x c -> 10 * x + digitToInt c) 0

trim :: Text -> Text
trim = Text.init . Text.tail

parseOf :: Text -> Token
parseOf txt =
    let (prefix, txt'  ) = Text.span  isDigit txt
        ("to"  , suffix) = Text.break isDigit txt'
    in  Of (toInt prefix, toInt suffix)

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
    | OpenBracket
    | CloseBracket
    | OpenProductType
    | OpenSumType
    | CloseBrace
    | OpenProductValue
    | CloseAngle
    | ASCII Text
    | Comma
    | Bar
    | Colon
    | At
    | Star
    | Box
    | Arrow
    | Lambda
    | Pi
    | Given
    | Type
    | Fold
    | Data
    | Let
    | Equals
    | In
    | Of (Int, Int)
    | Label Text
    | Number Int
    | File Text
    | EOF
    deriving (Show)
}
