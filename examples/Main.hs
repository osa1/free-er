{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeOperators    #-}

module Main where

----------------------------------------------------------------------------------------------------
import           Control.Exception hiding (catch, throw)
import           Control.Monad.Eff
import           Data.IORef
import           Data.Proxy
----------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------

data State s a where
  Get    :: State s s
  Put    :: s -> State s ()
  Modify :: (s -> (s,a)) -> State s a

get :: Member (State s) r => Eff r s
get = send Get

put :: Member (State s) r => s -> Eff r ()
put = send . Put

runState :: s -> Eff (State s ': r) a -> Eff r (a,s)
runState s (Val v)   = return (v, s)
runState s (Eff u k) =
    case decomp u of
      Left u'          -> Eff u' (singleton (runState s . kApp k))
      Right Get        -> runState s (kApp k s)
      Right (Put s')   -> runState s' (kApp k ())
      Right (Modify f) -> let (s', a) = f s in runState s' (kApp k a)

evalState :: s -> Eff (State s ': r) a -> Eff r a
evalState s e = fst <$> runState s e

execState :: s -> Eff (State s ': r) a -> Eff r s
execState s e = snd <$> runState s e

runStateIO :: Member IO r => IORef s -> Eff (State s ': r) a -> Eff r (a,s)
runStateIO ref = loop
  where
    loop (Val v)   = (v,) <$> send (readIORef ref)
    loop (Eff u k) =
      case decomp u of
        Right Get        -> send (readIORef ref) >>= loop . kApp k
        Right (Put s)    -> send (writeIORef ref s) >> loop (kApp k ())
        Right (Modify f) -> send (atomicModifyIORef ref f) >>= loop . kApp k
        Left  u'         -> Eff u' (singleton (loop . kApp k))

statefulFac :: Member (State Int) r => Int -> Eff r ()
statefulFac 1 = return ()
statefulFac n = do
    a <- get
    put (n * a)
    statefulFac (n - 1)

runStatefulFac_IO :: Int -> IO Int
runStatefulFac_IO n = do
    ref <- newIORef 1 :: IO (IORef Int)
    snd <$> runM (runStateIO ref (statefulFac n))

runStatefulFac_pure :: Int -> Int
runStatefulFac_pure n = snd (run (runState 1 (statefulFac n)))

----------------------------------------------------------------------------------------------------

data Throw e a where
  Throw :: e -> Throw e a

throw :: (Member (Throw e) r) => e -> Eff r a
throw = send . Throw

catch :: (e -> a) -> Eff (Throw e ': r) a -> Eff r a
catch _ (Val a)   = return a
catch h (Eff u k) =
    case decomp u of
      Left  u'        -> Eff u' (singleton (catch h . kApp k))
      Right (Throw e) -> return (h e)

data StrError = StrError String deriving (Show)
data IntError = IntError Int    deriving (Show)

instance Exception StrError
instance Exception IntError

f1 :: (Member (Throw StrError) r, Member (Throw IntError) r) => Int -> Eff r Int
f1 _ = do
    throw (StrError "err")
    throw (IntError 123)

throwIO' :: (Member IO r, Exception e) => Proxy e -> Eff (Throw e ': r) a -> Eff r a
throwIO' _ (Val a)   = return a
throwIO' p (Eff u k) =
    case decomp u of
      Left  u'        -> Eff u' (singleton (throwIO' p . kApp k))
      Right (Throw e) -> send (throwIO e)

run_f1_pure :: Either IntError (Either StrError Int)
run_f1_pure = run $ catch Left $ catch (Right . Left) $ fmap (Right . Right) (f1 10)

return_f1 :: (Member (State Int) r, Member (Throw StrError) r1, Member (Throw IntError) r1) => Eff r (Eff r1 Int)
return_f1 = do
    i <- get
    return (f1 i)

get_f1 :: (Member (Throw StrError) r1, Member (Throw IntError) r1) => Eff r1 Int
get_f1 =
    let
      f1' :: (Member (Throw StrError) r1, Member (Throw IntError) r1) => Eff '[State Int] (Eff r1 Int)
      f1' = return_f1

      f'' :: (Member (Throw StrError) r1, Member (Throw IntError) r1) => Eff r1 Int
      f'' = fst (run (runState 123 f1'))
    in
      f''

f1_ :: (Member (Throw StrError) r, Member IO r) => Eff r Int
f1_ = throwIO' (Proxy :: Proxy IntError) (f1 10)

f1__ :: Member IO r => Eff r Int
f1__ = throwIO' (Proxy :: Proxy StrError) f1_

run_f1_IO :: IO Int
run_f1_IO = runM f1__

----------------------------------------------------------------------------------------------------

main :: IO ()
main = return ()
