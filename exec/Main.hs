{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Annah.Core as Annah
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core   as Morte
import qualified Morte.Import as Morte
import Options.Applicative
import System.IO (stderr)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

main :: IO ()
main = do
    execParser $ info (helper <*> pure ())
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Annah is a medium-level language that is a superset of \
                     \Morte.  Use this compiler to desugar Annah code to Morte \
                     \code."
        )
    txt <- Text.getContents
    ae  <- throws (Annah.exprFromText txt)
    let me = Annah.desugar ae
    Text.putStrLn (Morte.pretty (Morte.normalize me))
