module ShiTT.Meta where 

import qualified Data.IntMap as I
import ShiTT.Syntax
import Data.IORef
import System.IO.Unsafe

data MetaEntry = Unsolved | Solved Value
  deriving Show 

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