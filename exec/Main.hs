{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Annah.Core as Annah
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import Options.Applicative
import System.IO (stderr)

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
    case Annah.exprFromText txt of
        Left e -> throwIO e
        Right ae -> do
            let me = Annah.desugar ae
            Text.putStrLn (Morte.pretty me)
