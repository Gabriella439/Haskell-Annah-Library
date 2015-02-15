module Main where

import Annah.Parser (exprFromText, prettyParseError)
import Annah.Core
import Data.Monoid (mempty)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (typeOf, normalize, prettyTypeError)
import Options.Applicative
import System.IO (stderr)
import System.Exit (exitFailure)

using :: (e -> Text) -> Either e a -> Either Text a
using f (Left  e) = Left (f e)
using _ (Right a) = Right a

handle :: Either Text a -> IO a
handle e = case e of
    Left msg -> do
        Text.hPutStr stderr msg
        exitFailure
    Right a -> return a

main :: IO ()
main = do
    execParser $ info (helper <*> pure ())
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Type-check and normalize an Annah program, reading the \
                     \program from standard input, writing the program's type \
                     \to standard error, and writing the normalized program to\
                     \standard output"
        )
    inText <- Text.getContents

    (at, ae') <- handle (do
        ae  <- using prettyParseError             (exprFromText inText)
        mt  <- using prettyTypeError (typeOf (desugar ae))
        let at  = resugar (normalize  mt         )
        let ae' = resugar (normalize (desugar ae))
        return (at, ae') )

    Text.hPutStrLn stderr (prettyExpr at)
    Text.hPutStrLn stderr mempty
    Text.putStrLn (prettyExpr ae')
