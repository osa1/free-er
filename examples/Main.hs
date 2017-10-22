{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Main where

----------------------------------------------------------------------------------------------------
import           Control.Exception hiding (catch, throw)
import           Control.Monad.Eff
import           Data.IORef
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
    _ <- throw (StrError "err")
    throw (IntError 123)

throwIO' :: forall e r a . (Member IO r, Exception e) => Eff (Throw e ': r) a -> Eff r a
throwIO' (Val a)   = return a
throwIO' (Eff u k) =
    case decomp u of
      Left  u'        -> Eff u' (singleton (throwIO' . kApp k))
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
f1_ = throwIO' @IntError (f1 10)

f1__ :: Member IO r => Eff r Int
f1__ = throwIO' @StrError f1_

run_f1_IO :: IO Int
run_f1_IO = runM f1__

----------------------------------------------------------------------------------------------------

data Trace a where
  Trace :: String -> Trace ()

trace :: Member Trace r => String -> Eff r ()
trace = send . Trace

runTrace :: Member IO r => Eff (Trace ': r) a -> Eff r a
runTrace (Val v) = return v
runTrace (Eff u k) = case decomp u of
    Left u' -> Eff u' (singleton (runTrace . kApp k))
    Right (Trace str) -> do
      send (putStrLn str)
      runTrace (kApp k ())

----------------------------------------------------------------------------------------------------

data Reader s a where
  Ask :: Reader s s

ask :: Member (Reader s) r => Eff r s
ask = send Ask

-- TODO: local

runReader :: s -> Eff (Reader s ': r) a -> Eff r a
runReader _ (Val v) = return v
runReader s (Eff u k) = case decomp u of
    Left u' ->
      Eff u' (singleton (runReader s . kApp k))
    Right Ask ->
      runReader s (kApp k s)

----------------------------------------------------------------------------------------------------

-- http://okmij.org/ftp/Haskell/extensible/Eff1.hs

-- The yield request: reporting the value of type a and suspending
-- the coroutine. Resuming with the value of type b
data Yield a b ret where
  Yield :: a -> (b -> ret) -> Yield a b ret

yield :: Member (Yield a b) r => a -> (b -> ret) -> Eff r ret
yield arg cont = send (Yield arg cont)

yield' :: Member (Yield a b) r => a -> Eff r b
yield' arg = send (Yield arg id)

data Coroutine r a b ret
  = CoroutineDone ret
  | CoroutineContinue a (b -> Eff r (Coroutine r a b ret))

runCoroutine :: Eff (Yield a b ': r) ret -> Eff r (Coroutine r a b ret)
runCoroutine (Val v) = return (CoroutineDone v)
runCoroutine (Eff u k) = case decomp u of
    Left u' ->
      Eff u' (singleton (runCoroutine . kApp k))
    Right (Yield val cont) ->
      -- val  :: a
      -- cont :: b -> ret
      return (CoroutineContinue val (\b -> runCoroutine (kApp k (cont b))))

yieldInt :: Member (Yield Int ()) r => Int -> Eff r ()
yieldInt = yield'

th1 :: Member (Yield Int ()) r => Eff r ()
th1 = yieldInt 1 >> yieldInt 2

c1 :: IO ()
c1 = runM (runTrace (runCoroutine th1 >>= loop))
 where
   loop (CoroutineContinue x k) = do
     trace ("Coroutine step: " ++ show (x :: Int))
     k () >>= loop
   loop (CoroutineDone ret) =
     trace ("Done with " ++ show ret)

th2 :: (Member (Yield Int ()) r, Member (Reader Int) r) => Eff r ()
th2 = ask >>= yieldInt >> (ask >>= yieldInt)

c2 :: IO ()
c2 = runM (runTrace (runReader (10 :: Int) (runCoroutine th2 >>= loop)))
  where
    loop (CoroutineContinue x k) = do
      trace ("Coroutine step: " ++ show (x :: Int))
      k () >>= loop
    loop (CoroutineDone ret) =
      trace ("Done with " ++ show ret)

----------------------------------------------------------------------------------------------------

main :: IO ()
main = return ()
