module Main where

import qualified Annah.Parser as Annah
import qualified Annah.Core   as Annah
import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import Options.Applicative
import System.IO (stderr)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right a) = return a

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
    ae     <- throws (Annah.exprFromText inText)
    ae'    <- Annah.load ae
    let me = Annah.desugar ae'
    mt     <- throws (Morte.typeOf me)
    let at   = Annah.resugar (Morte.normalize mt)
    let ae'' = Annah.resugar (Morte.normalize me)

    Text.hPutStrLn stderr (Annah.prettyExpr at)
    Text.hPutStrLn stderr mempty
    Text.putStrLn (Annah.prettyExpr ae'')
