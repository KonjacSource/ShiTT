module ShiTT.Meta where

import qualified Data.IntMap as I
import ShiTT.Syntax
import Data.IORef
import System.IO.Unsafe

-- Meta Context
----------------
data MetaEntry = Unsolved | Solved Value
  deriving Show

solved :: MetaEntry -> Bool 
solved Unsolved = False 
solved _ = True

runIO = unsafeDupablePerformIO

nextMeta :: IORef Int
nextMeta = runIO $ newIORef 0
{-# noinline nextMeta #-}

mctx :: IORef (I.IntMap MetaEntry)
mctx = runIO $ newIORef mempty
{-# noinline mctx #-}

lookupMeta :: MetaId -> MetaEntry
lookupMeta m = runIO $ do
  ms <- readIORef mctx
  case I.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mctx mempty

allSolved :: IO Bool
allSolved = do
  ms <- readIORef mctx
  pure $ all solved ms

-- Options
-----------

withoutKRef :: IORef Bool 
withoutKRef = runIO $ newIORef False 

-- Other Global
---------------

allUnmatchableTypes :: IORef [Name]
allUnmatchableTypes = runIO $ newIORef []