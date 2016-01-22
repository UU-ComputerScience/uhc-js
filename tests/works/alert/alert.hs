main = do
  putStrLn "alert"
  alert 123


foreign import js "alert"
  alert :: Int -> IO ()
