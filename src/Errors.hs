module Errors where

import Control.Exception (Exception, throwIO)

data Error
  = VerifyError String
  | ElaborateError String

instance Exception Error

instance Show Error where
  show (VerifyError msg) = "verify: " ++ msg
  show (ElaborateError msg) = msg

throwUnless :: Bool -> Error -> IO ()
throwUnless True err = return ()
throwUnless False err = throwIO err
