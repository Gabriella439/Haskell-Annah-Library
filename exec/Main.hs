{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import Morte.Core (Path(..))
import Options.Applicative
import System.IO (stderr)

import qualified Annah.Core                as Annah
import qualified Annah.Parser              as Annah
import qualified Data.Text.Lazy.IO         as Text
import qualified Filesystem.Path.CurrentOS as Filesystem
import qualified Morte.Core                as Morte
import qualified Morte.Import              as Morte

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

parser :: Parser (Maybe String)
parser = optional
    (   strArgument
        (   metavar "FILE"
        <>  help "File to desugar"
        )
    )

main :: IO ()
main = do
    mFile <- execParser $ info (helper <*> parser)
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Annah is a medium-level language that is a superset of \
                     \Morte.  Use this compiler to desugar Annah code to Morte \
                     \code."
        )
    txt <- case mFile of
        Nothing   -> Text.getContents
        Just file -> Text.readFile file
    ae  <- throws (Annah.exprFromText txt)
    let me = Annah.desugar ae
    -- Only statically link the Morte expression for type-checking
    me' <- Morte.load (fmap (File . Filesystem.decodeString) mFile) me
    mt  <- throws (Morte.typeOf me')
    -- Return the dynamically linked Morte expression
    Text.putStrLn (Morte.pretty (Morte.normalize me))
