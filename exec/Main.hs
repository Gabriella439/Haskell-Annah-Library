{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Annah.Parser as Annah
import qualified Annah.Core   as Annah
import Control.Concurrent.Async (async)
import Control.Exception (Exception, throwIO)
import qualified Control.Foldl as Fold
import qualified Data.HashMap.Strict as HashMap
import Data.Text.Lazy (fromStrict)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import Options.Applicative
import System.IO (stderr)
import Turtle hiding (stderr, e)
import Prelude hiding (FilePath)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right a) = return a

options :: Parser Bool
options = switch (long "dynamic" <> short 'd')

main :: IO ()
main = do
    dynamic <- execParser $ info (helper <*> options)
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Type-check and normalize an Annah program, reading the \
                     \program from standard input, writing the program's type \
                     \to standard error, and writing the normalized program to\
                     \standard output"
        )
    let io = fmap (Annah.dynamic . HashMap.fromList) (fold files Fold.list)
    getLink <- if dynamic
        then fmap wait (async io)
        else return (return Annah.static)

    inText <- Text.getContents
    ae     <- throws (Annah.exprFromText inText)
    ae'    <- Annah.loadExpr ae
    let me = Annah.desugar ae'
    mt     <- throws (Morte.typeOf me)
    link   <- getLink
    let at   = Annah.resugar link (Morte.normalize mt)
    let ae'' = Annah.resugar link (Morte.normalize me)

    Text.hPutStrLn stderr (Annah.prettyExpr at)
    Text.hPutStrLn stderr mempty
    Text.putStrLn (Annah.prettyExpr ae'')

files :: Shell (Morte.Expr, FilePath)
files = do
    dir        <- liftIO pwd
    -- This adds a trailing slash, otherwise `stripPrefix` will not work
    let dir' = dir </> mempty
    file       <- lstree dir
    file'      <- liftIO (realpath file)
    False      <- liftIO (testdir file')
    txt        <- liftIO (strict (input file'))
    Right expr <- return (Annah.exprFromText (fromStrict txt))
    expr'      <- liftIO (fmap Annah.desugar (Annah.loadExpr expr))
    Right _    <- return (Morte.typeOf expr')
    Just  rel  <- return (stripPrefix dir' file')
    let rel' = if basename rel == "=" then dirname rel else rel
    return (Morte.normalize expr', rel')
