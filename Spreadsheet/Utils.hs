---------------
-- UTILITIES --
---------------

module Spreadsheet.Utils (
  err
) where

-- Error reporting with line/column info.
err (l, c) msg = error (msg ++ " at line " ++ (show l) ++ ", column " ++ (show c))
