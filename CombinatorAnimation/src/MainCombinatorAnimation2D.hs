-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Combinatory logic animation.
--
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Main where


import Combinators
import CombinatorAnimation
import Paths_CombinatorAnimation (getDataDir)

import ConeCanvas.OntoControl
import ConeCanvas.OntoModel
--import Control.Concurrent (yield)
import ConeCanvas.Frontend.GtkCairo
import ConeCanvas.Preferences



import Control.Monad (when)
import Data.IORef
import Graphics.UI.Gtk
import System.FilePath ((</>))

main:: IO()
main = do
    dataDir   <- getDataDir
    icons     <- getIconNames ".png" (dataDir </> "Icons")
    window    <- ofInitGUI GtkCairoFrontend (undefined :: EditTerm VarString)
    ontoCigolStateRef <- newIORef (OntoCigolState)
    _ontoCigolState <- readIORef ontoCigolStateRef
    condPrefs <- loadPrefs
    (interface,GtkFrame da) <- initOntoPanel False standardIKS [] (icons,".png",dataDir </> "Icons") () condPrefs

    box <- vBoxNew True 2
    radioIKS <- radioButtonNewWithLabel "IKS"
    radioBCKW <- radioButtonNewWithLabelFromWidget radioIKS "BCKW"

    textEntry <- entryNew

    _cid <- radioIKS `on` buttonActivated $ setComb standardIKS textEntry interface
    _cid <- radioBCKW `on` buttonActivated $ setComb standardBCKW textEntry interface

    _cid <- textEntry `on` entryActivate $ do
        text <- entryGetText textEntry
        iks <- toggleButtonGetActive radioIKS
        bckw <- toggleButtonGetActive radioBCKW
        when iks $
            case parseErr text of
                Left str -> do
                    putStrLn ("Parse error: " ++ str)
                    flush
                    return ()
                Right term -> do
                    let model = toOntoModel (TermIKS term)
                    condPos <- ontoSelectFirst model
                    case condPos of
                        Nothing -> return ()
                        Just p -> omSetModel interface (OSCurrent p) []
        when bckw $
            case parseErr text of
                Left str -> do
                    putStrLn ("Parse error: " ++ str)
                    flush
                    return ()
                Right term -> do
                    let model = toOntoModel (TermBCKW term)
                    condPos <- ontoSelectFirst model
                    case condPos of
                        Nothing -> return ()
                        Just p -> omSetModel interface (OSCurrent p) []

    entrySetText textEntry (showTerm (toTerm (selModelFromRoot standardIKS)))

    buttonbox <- hButtonBoxNew
    buttonBoxSetLayout buttonbox ButtonboxCenter

    stepButton <- buttonNewWithLabel "Step "
    _cid <- stepButton `on` buttonActivated $ stepIt ontoCigolStateRef interface textEntry
    runButton <- checkButtonNewWithLabel "Run  "
    _cid <- runButton `on` toggled $ do
        pressed <- toggleButtonGetActive runButton
        runIt pressed ontoCigolStateRef interface textEntry runButton
--    stopButton <- buttonNewWithLabel "stop"
--    resetButton <- buttonNewWithLabel "reset"
    containerAdd buttonbox stepButton
    containerAdd buttonbox runButton
--    containerAdd buttonbox stopButton
--    containerAdd buttonbox resetButton


    -- Pack them into a box, then show all the widgets
    boxPackStart box radioIKS PackGrow 2
    boxPackStart box radioBCKW PackGrow 2
    vbox <- vBoxNew False 0
    boxPackStart vbox da PackGrow 0
    boxPackStart vbox textEntry PackNatural 0
    boxPackStart vbox buttonbox PackNatural 0
    boxPackStart vbox box PackNatural 0


    let GtkWindow wi = window
    containerAdd wi vbox
    ofStartGUI window





