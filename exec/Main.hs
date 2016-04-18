{-# LANGUAGE OverloadedStrings #-}

module Main where

import Annah.Core (Data(..), Expr(..), Type(..))
import Control.Applicative ((<|>))
import Control.Exception (Exception, throwIO)
import Control.Monad (forM_)
import Data.Monoid (mempty)
import Data.Text.Lazy (fromStrict)
import Filesystem.Path (FilePath, (</>))
import Morte.Core (Path(..), Var(..))
import Options.Applicative
import Prelude hiding (FilePath)
import System.IO (stderr)

import qualified Annah.Core                as Annah
import qualified Annah.Parser              as Annah
import qualified Data.Text.Lazy            as Text
import qualified Data.Text.Lazy.IO         as Text
import qualified Filesystem
import qualified Filesystem.Path.CurrentOS as Filesystem
import qualified Morte.Core                as Morte
import qualified Morte.Import              as Morte

throws :: Exception e => Either e a -> IO a
throws (Left  e) = throwIO e
throws (Right r) = return r

data Mode = Default | Compile FilePath | Desugar | Types

parser :: Parser Mode
parser
    =   subparser
        (   command "compile"
            (info (helper <*> (Compile <$> parseFilePath))
                (   fullDesc
                <>  header "annah compile - Compile Annah code"
                <>  progDesc "Compile an Annah program located at the given \
                             \file path.  Prefer this subcommand over reading \
                             \from standard input when you want remote \
                             \references to be resolved relative to that \
                             \file's path"
                )
            )
        <>  metavar "compile"
        )
    <|> subparser
        (   command "desugar"
            (info (helper <*> pure Desugar)
                (   fullDesc
                <>  header "annah desugar - Desugar Annah code"
                <>  progDesc "Desugar an Annah program to the equivalent Morte \
                             \program, reading the Annah program from standard \
                             \input and writing the Morte program to standard \
                             \output."
                )
            )
        <>  metavar "desugar"
        )
    <|> subparser
        (   command "types"
            (   info (helper <*> pure Types)
                (   fullDesc
                <>  header "annah types - Compile an Annah datatype definition"
                <>  progDesc "Translate an Annah datatype definition to the \
                             \equivalent set of files, reading the datatype \
                             \definition from standard input.  This creates \
                             \one output directory for each type with one file \
                             \underneath each directory per data constructor \
                             \associated with that type."
                )
            )
        <>  metavar "types"
        )
    <|> pure Default
  where
    parseFilePath =
        fmap Filesystem.decodeString
            (strArgument (metavar "FILEPATH" <> help "Path to file to compile"))

main :: IO ()
main = do
    mode <- execParser $ info (helper <*> parser)
        (   fullDesc
        <>  header "annah - A strongly typed, purely functional language"
        <>  progDesc "Annah is a medium-level language that is a superset of \
                     \Morte.  Use this compiler to desugar Annah code to Morte \
                     \code."
        )
    case mode of
        Default -> do
            txt <- Text.getContents
            ae  <- throws (Annah.exprFromText txt)
            let me = Annah.desugar ae
            -- Only statically link the Morte expression for type-checking
            me' <- Morte.load Nothing me
            mt  <- throws (Morte.typeOf me')
            -- Return the dynamically linked Morte expression
            Text.putStrLn (Morte.pretty (Morte.normalize me))
        Compile file -> do
            txt <- Text.readFile (Filesystem.encodeString file)
            ae  <- throws (Annah.exprFromText txt)
            let me = Annah.desugar ae
            -- Only statically link the Morte expression for type-checking
            me' <- Morte.load (Just (File file)) me
            mt  <- throws (Morte.typeOf me')
            -- Return the dynamically linked Morte expression
            Text.putStrLn (Morte.pretty (Morte.normalize me))
        Desugar -> do
            txt <- Text.getContents
            ae  <- throws (Annah.exprFromText txt)
            Text.putStrLn (Morte.pretty (Annah.desugar ae))
        Types -> do
            -- TODO: Handle duplicate type and data constructor names
            txt <- Text.getContents
            ts  <- throws (Annah.typesFromText txt)
            let write file txt =
                    Filesystem.writeTextFile file (Text.toStrict txt <> "\n")
            let named = Filesystem.fromText . Text.toStrict
            forM_ ts (\t -> do
                let typeDir = named (typeName t)
                let typeAnnahFile = named (typeName t <> ".annah")
                let typeMorteFile = typeDir </> "@"
                let foldAnnahFile = typeDir </> named (typeFold t <> ".annah")
                let foldMorteFile = typeDir </> named (typeFold t)

                Filesystem.createDirectory True typeDir
                write typeAnnahFile (txt <> "in   " <> typeName t)
                let e0 = Family ts (Var (V (typeName t) 0))
                let typeTxt = Morte.pretty (Morte.normalize (Annah.desugar e0))
                write typeMorteFile typeTxt

                if typeFold t /= "_"
                    then do
                        write foldAnnahFile (txt <> "in   " <> typeFold t)
                        let e1 = Family ts (Var (V (typeFold t) 0))
                        let foldTxt =
                                Morte.pretty (Morte.normalize (Annah.desugar e1))
                        write foldMorteFile foldTxt
                    else return ()

                forM_ (typeDatas t) (\d -> do
                    let dataAnnahName = named (dataName d <> ".annah")
                    let dataMorteName = named (dataName d)
                    let dataAnnahFile = typeDir </> dataAnnahName
                    let dataMorteFile = typeDir </> dataMorteName

                    write dataAnnahFile (txt <> "in   " <> dataName d)

                    let e2 = Family ts (Var (V (dataName d) 0))
                    let dataTxt =
                            Morte.pretty (Morte.normalize (Annah.desugar e2))
                    write dataMorteFile dataTxt ) )
