module Paths_natural_deduction (
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
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "F:\\Projects\\natural-deduction\\.cabal-sandbox\\bin"
libdir     = "F:\\Projects\\natural-deduction\\.cabal-sandbox\\x86_64-windows-ghc-7.8.3\\natural-deduction-0.1.0.0"
datadir    = "F:\\Projects\\natural-deduction\\.cabal-sandbox\\x86_64-windows-ghc-7.8.3\\natural-deduction-0.1.0.0"
libexecdir = "F:\\Projects\\natural-deduction\\.cabal-sandbox\\natural-deduction-0.1.0.0"
sysconfdir = "F:\\Projects\\natural-deduction\\.cabal-sandbox\\etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "natural_deduction_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "natural_deduction_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "natural_deduction_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "natural_deduction_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "natural_deduction_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
