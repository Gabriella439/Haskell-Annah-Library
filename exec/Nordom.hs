{-# LANGUAGE OverloadedStrings #-}

import qualified Annah.Core   as Annah
import qualified Annah.Parser as Annah
import Control.Exception (throwIO)
import Control.Monad (when)
import Control.Monad.Trans.State (State, get, put, evalState)
import Data.Char (toLower)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid ((<>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy    as Text
import qualified Data.Text.Lazy.IO as Text
import Morte.Core (Const(..), Expr(..), Var(..), X)
import qualified Morte.Core   as Morte
import qualified Morte.Import as Morte
import System.Environment (getArgs)
import System.Process (system)
import qualified System.IO as IO
import Turtle hiding (Text, lower)

intToText :: Int -> Text
intToText n = Text.pack (show n)

lower :: Text -> Text
lower txt = case Text.uncons txt of
    Nothing -> txt
    Just (c, txt') -> Text.cons (toLower c) txt'

rename :: Expr a -> Expr a
rename expr = evalState (_rename expr) HashMap.empty

_rename :: Expr a -> State (HashMap Text Int) (Expr a)
_rename (Lam x _A b) = do
    m <- get
    let n = case HashMap.lookup x m of
            Nothing -> 0
            Just m  -> m
    let n' = n + 1
    n' `seq` put (HashMap.insert x n' m)
    let x' = lower x <> intToText n

    _A' <- _rename _A
    b'  <- _rename (Morte.subst x 0 (Var (V x' 0)) b)
    return (Lam x' _A' b')
_rename (Pi x _A b) = do
    m <- get
    let n = case HashMap.lookup x m of
            Nothing -> 0
            Just m  -> m
    let n' = n + 1
    n' `seq` put (HashMap.insert x n' m)
    let x' = lower x <> intToText n

    _A' <- _rename _A
    b'  <- _rename (Morte.subst x 0 (Var (V x' 0)) b)
    return (Pi x' _A' b')
_rename (App f a) = do
    f' <- _rename f
    a' <- _rename a
    return (App f' a')
_rename e = return e

_toHaskell :: Expr X -> Text
_toHaskell (Lam x _A b) = "\\" <> x <> " -> " <> _toHaskell b
_toHaskell (Var (V x 0)) = x
_toHaskell (App f a) = "(" <> _toHaskell f <> ") (" <> _toHaskell a <> ")"
_toHaskell (Pi _ _ _) = "()"

toHaskell :: Expr X -> Text
toHaskell e = Text.unlines
    [ "import Annah.Haskell"
    , ""
    , "main = io'ToIO (" <> _toHaskell e <> ")"
    ]

throws x =
    case x of
        Left  e -> throwIO e
        Right a -> return a

main = do
    args <- getArgs
    url  <- case args of
        [url] -> return url
        _     -> do
            err "Usage: ./nordom URL"
            exit (ExitFailure 1)
    let me = Morte.Embed (Morte.URL url)
    err "[+] Resolving imports"
    me' <- Morte.load me
    err "[+] Type-checking"
    mt <- throws (Morte.typeOf (Morte.normalize me'))
    when (mt /= t) (do
        let msg = unlines
                [ "Error: Forbidden type for expression at: " <> url
                , ""
                , "Expected type: #IO #Prod0"
                , "Actual   type: " <> Text.unpack (Morte.pretty mt)
                ]
        throwIO (userError msg) )
    err "[+] Compiling"
    Text.writeFile "tmp.hs" (toHaskell (rename (Morte.normalize me')))
    proc "stack" ["ghc", "tmp.hs"] empty
    Text.putStrLn "[+] Executing"
    system "./tmp"
    shell "rm tmp*" empty

t :: Expr X
t = Pi "IO" (Const Star) (Pi "GetLine_" (Pi "_" (Pi "_" (Pi "S" (Const Star) (Pi "N" (Var (V "S" 0)) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Var (V "S" 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Var (V "IO" 0))) (Var (V "IO" 0))) (Pi "PutLine_" (Pi "_" (Pi "S" (Const Star) (Pi "N" (Var (V "S" 0)) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Pi "C" (Pi "_" (Var (V "S" 0)) (Var (V "S" 0))) (Var (V "S" 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (Pi "_" (Var (V "IO" 0)) (Var (V "IO" 0)))) (Pi "Pure_" (Pi "_" (Pi "Prod0" (Const Star) (Pi "Make" (Var (V "Prod0" 0)) (Var (V "Prod0" 0)))) (Var (V "IO" 0))) (Var (V "IO" 0)))))
