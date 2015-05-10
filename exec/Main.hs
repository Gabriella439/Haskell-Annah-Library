{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Annah.Core   as Annah
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import qualified Data.Text.Lazy.IO as Text
import qualified Morte.Core as Morte
import qualified Morte.Import as Morte
import qualified Morte.Parser as Morte
import Options.Applicative
import System.IO (stderr)

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right a) = return a

fmapL :: (e -> f)  -> Either e a -> Either f a
fmapL k (Left  e) = Left (k e)
fmapL _ (Right a) = Right a

data Mode = Desugar | Resugar | Compile

mode :: Parser Mode
mode =  subparser (command "desugar" (info (pure Desugar)
            (   fullDesc
            <>  header "annah - A strongly typed, purely functional language"
            <>  progDesc "Desugar an Annah program into a Morte program"
            ) ))
    <|> subparser (command "resugar" (info (pure Resugar)
            (   fullDesc
            <>  header "annah - A strongly typed, purely functional language"
            <>  progDesc "Resugar a Morte program into an Annah program"
            ) ))
    <|> subparser (command "compile" (info (pure Compile)
            (   fullDesc
            <>  header "annah - A strongly typed, purely functional language"
            <>  progDesc "Compile an Annah program"
            ) ))

main :: IO ()
main = do
    m <- execParser $ info (helper <*> mode)
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Annah is a medium-level language that is a superset of \
                     \Morte.  Use the Annah compiler to desugar Annah to Morte, \
                     \to resugar Morte to Annah, or to compile an Annah program."
        )

    case m of
        Desugar -> do
            txt <- Text.getContents
            ae  <- throws (Annah.exprFromText txt)
            let me = Annah.desugar ae
            Text.putStrLn (Morte.pretty me)
        Resugar -> do
            txt <- Text.getContents
            me  <- throws (Morte.exprFromText txt)
            let ae = Annah.resugar me
            Text.putStrLn (Morte.pretty ae)
        Compile -> do
            txt <- Text.getContents
            ae  <- throws (Annah.exprFromText txt)
            let me = Annah.desugar ae
            me' <- Morte.load me
            mt  <- throws (fmapL (Annah.resugarTypeError) (Morte.typeOf me'))
            let at  = Annah.resugar (Morte.normalize mt)
            let ae' = Annah.resugar (Morte.normalize me')
            Text.hPutStrLn stderr (Morte.pretty at)
            Text.hPutStrLn stderr mempty
            Text.putStrLn (Morte.pretty ae')
