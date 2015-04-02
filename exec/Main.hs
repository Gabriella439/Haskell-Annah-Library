module Main where

import qualified Annah.Parser as Annah
import qualified Annah.Core   as Annah
import Control.Exception (Exception, throwIO)
import qualified Control.Foldl as Fold
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import Options.Applicative
import System.IO (stderr)
import Turtle hiding (stderr)
import Prelude hiding (FilePath)

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
    ae'    <- Annah.loadExpr ae
    let me = Annah.desugar ae'
    mt     <- throws (Morte.typeOf me)
    h      <- fmap HashMap.fromList (fold files Fold.list)
    let at   = Annah.resugar (Annah.dynamic h) (Morte.normalize mt)
    let ae'' = Annah.resugar (Annah.dynamic h) (Morte.normalize me)

    Text.hPutStrLn stderr (Annah.prettyExpr at)
    Text.hPutStrLn stderr mempty
    Text.putStrLn (Annah.prettyExpr ae'')

files :: Shell (Morte.Expr, FilePath)
files = do
    dir  <- liftIO pwd
    file <- ls dir
    txt        <- liftIO (strict (input file))
    Right expr <- return (Annah.exprFromText (fromStrict txt))
    expr'      <- liftIO (fmap Annah.desugar (Annah.loadExpr expr))
    Right _    <- return (Morte.typeOf expr')
    return (Morte.normalize expr', basename file)
