module Main where

import qualified Annah.Parser as Annah
import qualified Annah.Core   as Annah
import Data.Monoid (mempty)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy    as Text
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import Options.Applicative
import System.IO (stderr)
import System.Exit (exitFailure, exitSuccess)

using :: (e -> Text) -> Either e a -> Either Text a
using f (Left  e) = Left (f e)
using _ (Right a) = Right a

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

    let compile = do
            ae <- using Annah.prettyParseError (Annah.exprFromText inText)
            let me  = Annah.desugar ae
            mt <- using Morte.prettyTypeError (Morte.typeOf me)
            let at  = Annah.resugar (Morte.normalize mt)
            let ae' = Annah.resugar (Morte.normalize me)
            return (at, ae')

    case compile of
        Left msg -> do
            Text.hPutStr stderr msg
            exitFailure
        Right (at, ae') -> do
            Text.hPutStrLn stderr (Annah.prettyExpr at)
            Text.hPutStrLn stderr mempty
            Text.putStrLn (Annah.prettyExpr ae')
            exitSuccess
