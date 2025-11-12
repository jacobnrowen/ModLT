module Main (
    main
) where

import System.Environment (getArgs)
import ProcessTDuc
import ProcessStructure

main :: IO ()
main = do
    args <- getArgs
    if length args >= 2 then do
        strucFile <- readFile (head args)
        tducFiles <- mapM readFile (drop 2 args)
        let procdStrucFile = getStrucsFile strucFile
        let tducs = map getTransduction tducFiles
        writeFile (args!!1) (getResults procdStrucFile tducs)
    else putStrLn ("Error: modlt requires at least two command line arguments: " ++
        "a structure input file, an output file path, and one or more transduction files")