main = do
  putStrLn "alert"
  alert 123


foreign import js "alert(%1)"
  alert :: Int -> IO ()
