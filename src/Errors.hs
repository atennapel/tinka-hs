module Errors where

import Control.Exception (Exception, throwIO)

data Error
  = VerifyError String
  deriving (Show)

instance Exception Error

throwUnless :: Bool -> Error -> IO ()
throwUnless True err = return ()
throwUnless False err = throwIO err
