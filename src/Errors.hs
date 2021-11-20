module Errors (throw, Error(..)) where

import Control.Exception (Exception)
import qualified Control.Exception as E

newtype Error = Error String

instance Show Error where
  show (Error msg) = msg

instance Exception Error

throw :: String -> IO a
throw = E.throw . Error
