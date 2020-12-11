module Main where

import Data.Time.Clock
import Lib ( readLines,
             mergeSort,
             quickSort,
             bitonicSort,
           )
import Data.List (sort)
-- import qualified Data.ByteString as B
import qualified Data.Vector as V
import Data.Vector ((!))
import Control.DeepSeq (force)
import Data.String ( fromString )

main :: IO ()
main = do 
    v <- readLines "res/shuffledwords.txt"
    time "quickSort" (quickSort v)
    time "sort" $ sort (V.toList v)
    time "mergeSort" (mergeSort v) 
    time "bitonicsort" (bitonicSort (fromString "zz") v) 
    where
    time msg a = do
        start <- getCurrentTime
        let a' = force a
        end <- a' `seq` getCurrentTime
        putStrLn $ msg ++ ": " ++ show (diffUTCTime end start)
