{-# LANGUAGE ExistentialQuantification, GADTs, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, LambdaCase #-}
module Remorse.Free where
import Remorse.Sequence
import Remorse.Internal
import Control.Monad
import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Monad.Trans 

data FreeT f m a = forall x . 
    FreeT (m (Step f x (FreeT f m x)))
          (Queue (Kleisli (FreeT f m)) x a)

data Step f x y = Stop x | Step (f y)

construct :: Monad m 
       => f (FreeT f m a) 
       -> FreeT f m a
construct = \f -> FreeT (return (Step f)) blank
{-# INLINE construct #-}

wrap :: (Monad m, Functor f) 
     => m (FreeT f m a)
     -> FreeT f m a 
wrap = \mf -> FreeT (mf >>= next) blank
{-# INLINE wrap #-}

extend :: Queue (Kleisli (FreeT f m)) x a
       -> FreeT f m x 
       -> FreeT f m a
extend t = \(FreeT h m) -> FreeT h (m >< t)
{-# INLINE extend #-}

next :: (Functor f, Monad m) => FreeT f m r -> m (Step f r (FreeT f m r))
next (FreeT mstep ks) = mstep >>= \case
  Stop x -> case uncons ks of 
    Empty            -> return (Stop x)
    Kleisli f :| ks' -> next (extend ks' (f x))
  Step f             -> return (Step (fmap (extend ks) f))
{-# INLINABLE next #-}

instance Monad m => Functor (FreeT f m) where
    {-# INLINE fmap #-}
    fmap f  = extend (singleton (Kleisli (return . f)))

instance Monad m => Applicative (FreeT f m) where
  pure x = FreeT (return (Stop x)) blank
  (<*>) = ap

instance Monad m => Monad (FreeT f m) where
    return x = FreeT (return (Stop x)) blank
    {-# INLINE return #-}
    FreeT m ks >> f = FreeT m (ks >< singleton (Kleisli (\_ -> f)))
    {-# INLINE (>>) #-}
    (FreeT m ks) >>= f = FreeT m (ks >< singleton (Kleisli f))
    {-# INLINE (>>=) #-} 
    

instance Functor f => MonadTrans (FreeT f) where
  lift = \ma -> FreeT (ma >>= return . Stop) blank
  {-# INLINE lift #-}
  
instance (Functor f, MonadIO m) => MonadIO (FreeT f m) where
  liftIO  = wrap . liftM return . liftIO 

fold :: (Functor f, Monad m) 
     => (f x -> x)
     -> (m x -> x)
     -> (a -> x)
     -> FreeT f m a 
     -> x
fold construct wrap done = loop where
  loop (FreeT m ks) = wrap $ 
    liftM 
    (\case 
        Stop o    -> case uncons ks of 
          Empty            -> done o
          Kleisli f :| ks' -> loop (extend ks' (f o))
        Step ffo -> case uncons ks of 
          Empty         -> construct (fmap loop ffo)
          _             -> construct (fmap (loop . extend ks) ffo)
    ) m
{-# INLINABLE fold #-}

buildFreeT :: (Functor f, Monad m) 
           => (forall x.(f x -> x) -> (m x -> x) -> (r -> x) -> x)
           -> FreeT f m r
buildFreeT phi = phi construct wrap return
     




iterT ::  (Functor f, Monad m) 
      => (f (m a) -> m a) -> FreeT f m a -> m a
iterT phi = fold phi join return

iterTM :: (Functor f, Monad m, MonadTrans t, Monad (t m)) 
       =>  (f (t m a) -> t m a) -> FreeT f m a -> t m a
iterTM phi = fold phi (join . lift) (lift . return)

hoistFreeT :: (Monad m, Functor f) 
           => (forall x. m x -> n x) 
           -> FreeT f m a -> FreeT f n a
hoistFreeT phi (FreeT mstep ks) = FreeT 
  (phi $ liftM (\case Stop r  -> Stop r
                      Step ff -> Step (fmap (hoistFreeT phi) ff))
               mstep)
  (maps (\(Kleisli f) -> Kleisli (hoistFreeT phi . f)) ks)
{-# INLINABLE hoistFreeT #-}

transFreeT :: (Monad m, Functor f) 
           => (forall x . f x -> g x) 
           -> FreeT f m a -> FreeT g m a
transFreeT phi (FreeT mstep ks) = FreeT 
   (liftM (\case Stop r  -> Stop r
                 Step ff -> Step (phi $ fmap (transFreeT phi) ff)) 
          mstep)
   (maps (\(Kleisli f)  -> Kleisli (transFreeT phi . f)) 
         ks)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       
{-# INLINABLE transFreeT #-}

enlist :: Monad m => [a] -> FreeT ((,) a) m ()
enlist [] = return ()
enlist (a:as) = construct (a,enlist as)

printer :: Show a => FreeT ((,) a) IO () -> IO ()
printer = fold (\(a,io) -> print a >> io) join return
-- cutoff ::
--   (Functor f, Monad m) =>
--   Integer -> FreeT f m a -> FreeT f m (Maybe a)