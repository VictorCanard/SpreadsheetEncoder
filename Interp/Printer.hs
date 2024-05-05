module Interp.Printer (
  showsheet,
) where

import Data.List

showrow :: [Int] -> String
showrow row = intercalate ", " (map show row)

showsheet :: [[Int]] -> String
showsheet s = intercalate "\n" (map showrow s)
