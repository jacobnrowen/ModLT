module Main (
    main
) where

import System.Environment (getArgs)
import ProcessTDuc
import ProcessStructure

main :: IO ()
main = do
    args <- getArgs
    let (strucFPath,outFPath,validArgs) = getFirstArgs args
    if validArgs then do
        strucFile <- readFile strucFPath
        tducFiles <- mapM readFile (drop 2 args)
        let procdStrucFile = getStrucsFile strucFile
        let tducs = map getTransduction tducFiles
        writeFile outFPath (getResults procdStrucFile tducs)
    else putStrLn ("Error: ModLT requires at least two command line arguments: " ++
        "a structure input file, an output file path, and one or more transduction files")

getFirstArgs :: [String] -> (String,String,Bool)
--Check if the first two arguments are present and retrive them if they are
getFirstArgs (arg0:(arg1:_)) = (arg0,arg1,True)
getFirstArgs _ = ("","",False)