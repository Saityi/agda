{-# LANGUAGE CPP #-}

{-| Agda main module.
-}
module Agda.Main where

import Control.Monad.State
import Control.Applicative

import Data.Maybe

import System.Environment
import System.Exit
import System.Console.GetOpt

import Agda.Syntax.Position (Range)
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract.Name (toTopLevelModuleName)

import Agda.Interaction.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.EmacsTop (mimicGHCi)
import Agda.Interaction.Imports (MaybeWarnings'(..))
import qualified Agda.Interaction.Imports as Imp
import qualified Agda.Interaction.Highlighting.Dot as Dot
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Pretty

import Agda.Compiler.Common (IsMain (..))
import Agda.Compiler.MAlonzo.Compiler (ghcBackend)
import Agda.Compiler.JS.Compiler (jsBackend)
import Agda.Compiler.UHC.Compiler (uhcBackend)
import Agda.Compiler.UHC.Bridge (uhcBackendEnabled)

import Agda.Compiler.Backend

import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.String

import Agda.VersionCommit

import qualified Agda.Utils.Benchmark as UtilsBench
import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Impossible
import Agda.Utils.Lens

#include "undefined.h"

builtinBackends :: [Backend]
builtinBackends =
  [ ghcBackend, jsBackend ] ++
  [ uhcBackend | uhcBackendEnabled ]

-- | The main function
runAgda :: [Backend] -> IO ()
runAgda backends = runAgda' $ builtinBackends ++ backends

runAgda' :: [Backend] -> IO ()
runAgda' backends = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  opts     <- liftIO $ runOptM $ parseBackendOptions backends argv
  case opts of
    Left  err        -> liftIO $ optionError err
    Right (bs, opts) -> do
      stBackends .= bs
      let enabled (Backend b) = isEnabled b (options b)
          bs' = filter enabled bs
      () <$ runAgdaWithOptions backends generateHTML (interaction bs') progName opts
      where
        interaction bs = backendInteraction bs $ defaultInteraction opts

defaultInteraction :: CommandLineOptions -> TCM (Maybe Interface) -> TCM ()
defaultInteraction opts
  | i         = runIM . interactionLoop
  | ghci      = mimicGHCi . (failIfInt =<<)
  | otherwise = (() <$)
  where
    i    = optInteractive     opts
    ghci = optGHCiInteraction opts

    failIfInt Nothing  = return ()
    failIfInt (Just _) = __IMPOSSIBLE__


-- | Run Agda with parsed command line options and with a custom HTML generator
runAgdaWithOptions
  :: [Backend]          -- ^ Backends only for printing usage and version information
  -> TCM ()             -- ^ HTML generating action
  -> (TCM (Maybe Interface) -> TCM a) -- ^ Backend interaction
  -> String             -- ^ program name
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM (Maybe a)
runAgdaWithOptions backends generateHTML interaction progName opts
      | optShowHelp opts    = Nothing <$ liftIO (printUsage backends)
      | optShowVersion opts = Nothing <$ liftIO (printVersion backends)
      | isNothing (optInputFile opts)
          && not (optInteractive opts)
          && not (optGHCiInteraction opts)
                            = Nothing <$ liftIO (printUsage backends)
      | otherwise           = do
          -- Main function.
          -- Bill everything to root of Benchmark trie.
          UtilsBench.setBenchmarking UtilsBench.BenchmarkOn
            -- Andreas, Nisse, 2016-10-11 AIM XXIV
            -- Turn benchmarking on provisionally, otherwise we lose track of time spent
            -- on e.g. LaTeX-code generation.
            -- Benchmarking might be turned off later by setCommandlineOptions

          Bench.billTo [] checkFile `finally_` do
            -- Print benchmarks.
            Bench.print

            -- Print accumulated statistics.
            printStatistics 20 Nothing =<< use lensAccumStatistics
  where
    checkFile = Just <$> do
      when (optInteractive opts) $ liftIO $ putStr splashScreen
      interaction $ do
        setCommandLineOptions opts
        hasFile <- hasInputFile
        -- Andreas, 2013-10-30 The following 'resetState' kills the
        -- verbosity options.  That does not make sense (see fail/Issue641).
        -- 'resetState' here does not seem to serve any purpose,
        -- thus, I am removing it.
        -- resetState
        if not hasFile then return Nothing else do
          file    <- getInputFile
          (i, mw) <- Imp.typeCheckMain file Imp.TypeCheck

          -- An interface is only generated if NoWarnings.
          result <- case mw of
            SomeWarnings ws -> do
              ws' <- applyFlagsToTCWarnings RespectFlags ws
              case ws' of
                []   -> return Nothing
                cuws -> tcWarningsToError cuws
            NoWarnings      -> return $ Just i

          reportSDoc "main" 50 $ pretty i

          whenM (optGenerateHTML <$> commandLineOptions) $
            generateHTML

          whenM (isJust . optDependencyGraph <$> commandLineOptions) $
            Dot.generateDot $ i

          whenM (optGenerateLaTeX <$> commandLineOptions) $
            LaTeX.generateLaTeX i

          return result



-- | Print usage information.
printUsage :: [Backend] -> IO ()
printUsage backends = do
  progName <- getProgName
  putStr $ usage standardOptions_ progName
  mapM_ (putStr . backendUsage) backends

backendUsage :: Backend -> String
backendUsage (Backend b) =
  usageInfo ("\n" ++ backendName b ++ " backend options") $
    map (fmap $ const ()) (commandLineFlags b)

-- | Print version information.
printVersion :: [Backend] -> IO ()
printVersion backends = do
  putStrLn $ "Agda version " ++ versionWithCommitInfo
  mapM_ putStrLn
    [ "  - " ++ name ++ " backend version " ++ ver
    | Backend Backend'{ backendName = name, backendVersion = Just ver } <- backends ]

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err = do
  prog <- getProgName
  putStrLn $ "Error: " ++ err ++ "\nRun '" ++ prog ++ " --help' for help on command line options."
  exitFailure

-- | Run a TCM action in IO; catch and pretty print errors.
runTCMPrettyErrors :: TCM () -> IO ()
runTCMPrettyErrors tcm = do
    r <- runTCMTop $ tcm `catchError` \err -> do
      s2s <- prettyTCWarnings' =<< Imp.errorWarningsOfTCErr err
      s1  <- prettyError err
      let ss = filter (not . null) $ s2s ++ [s1]
      unless (null s1) (liftIO $ putStr $ unlines ss)
      throwError err
    case r of
      Right _ -> exitSuccess
      Left _  -> exitFailure
  `catchImpossible` \e -> do
    putStr $ show e
    exitFailure

-- | Main
main :: IO ()
main = runAgda []
