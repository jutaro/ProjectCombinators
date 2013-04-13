-----------------------------------------------------------------------------
--
-- Module      :  BenchOntoCigol
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- | Benchmarks for the cigol package
--
-----------------------------------------------------------------------------

module Main where

import Combinators
import CombinatorAnimation
import Paths_CombinatorAnimation (getDataDir)

import ConeCanvas.Frontend.GtkCairo
import ConeCanvas.OntoModel
       (omAnimateFinishedCallback, OntoInterface(..), OntoFront(..),omSetPrefs)
import ConeCanvas.OntoControl

import Criterion.Config
import Criterion.Main
import Data.IORef
import Graphics.UI.Gtk
import System.FilePath ((</>))

import Control.Monad.IO.Class
import Debug.Trace (trace)


myConfig :: Config
myConfig = defaultConfig {
    cfgResamples    = ljust (5 * 1000),
    cfgSamples      = ljust 5}

main :: IO ()
main = defaultMainWith myConfig (return ()) [
        bench "gui1" $ nfIO (liftIO gui1)]

gui1 :: IO ()
gui1 =  do
    dataDir   <- getDataDir
    window    <- ofInitGUI GtkCairoFrontend (undefined :: EditTerm VarString)
    ontoCigolStateRef <- newIORef (OntoCigolState)
    _ontoCigolState <- readIORef ontoCigolStateRef
    icons     <- loadIconsCairo ".png" (dataDir </> "Icons")
    (interface,GtkFrame da) <- initOntoPanel True standardIKS [] icons ()
    condPrefs <- loadPrefs
    case condPrefs of
        Just prefs -> omSetPrefs interface prefs
        Nothing -> return ()

    let GtkWindow wi = window

    textEntry <- entryNew
    vbox <- vBoxNew False 0
    boxPackStart vbox da PackGrow 0
    boxPackStart vbox textEntry PackNatural 0


    containerAdd wi vbox

    _cid <- onDestroy wi mainQuit
    stopIt <- newIORef False
    idleAdd (trace "idleFunc': " $ do
        stopNow <- readIORef stopIt
        if stopNow
            then return False
            else do
                writeIORef stopIt True
                repeatIt wi ontoCigolStateRef interface textEntry 3 0
                return False) priorityHighIdle
    ofStartGUI window


repeatIt :: (Variable v, WidgetClass self) =>
                           self
                           -> IORef OntoCigolState
                           -> OntoInterface (EditTerm v)
                           -> Entry
                           -> Int
                           -> Int
                           -> IO ()
repeatIt window ontoCigolStateRef interface textEntry max = repeatIt'
  where repeatIt' n' = trace ("repeatIt': " ++ show n') $ do
            stepIt ontoCigolStateRef interface textEntry
            omAnimateFinishedCallback interface (if n' < max then repeatIt' (n' + 1)
                                             else widgetDestroy window)


