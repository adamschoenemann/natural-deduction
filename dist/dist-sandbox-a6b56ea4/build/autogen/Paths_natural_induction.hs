module Paths_natural_induction (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,1,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "F:\\Projects\\natural-induction\\.cabal-sandbox\\bin"
libdir     = "F:\\Projects\\natural-induction\\.cabal-sandbox\\x86_64-windows-ghc-7.8.3\\natural-induction-0.1.0.0"
datadir    = "F:\\Projects\\natural-induction\\.cabal-sandbox\\x86_64-windows-ghc-7.8.3\\natural-induction-0.1.0.0"
libexecdir = "F:\\Projects\\natural-induction\\.cabal-sandbox\\natural-induction-0.1.0.0"
sysconfdir = "F:\\Projects\\natural-induction\\.cabal-sandbox\\etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "natural_induction_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "natural_induction_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "natural_induction_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "natural_induction_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "natural_induction_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
