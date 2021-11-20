module TC where

type TC t = Either String t

err :: String -> TC t
err = Left

test :: Bool -> String -> TC ()
test True _ = return ()
test False msg = err msg
