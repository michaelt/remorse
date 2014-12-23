{-# LANGUAGE GADTs, ExistentialQuantification, RankNTypes, ScopedTypeVariables#-}
-- Author : Atze van der Ploeg
-- A purely functional catenable queue representation with
-- that turns takes a purely functional queue and turns in it into
-- a catenable queue, i.e. with the same complexity for (><) as for (|>)
-- Based on Purely functional data structures by Chris Okasaki 
-- section 7.2: Catenable lists
module Remorse.Sequence where
import Control.Category
import Prelude hiding ((.),id)
import Control.Applicative
import Control.Monad

infixr 5 <|
infixl 5 |>
infix 5 ><

data Cons c x y where
  Nil :: Cons c x x
  Cons :: c x y -> Cons c y z -> Cons c x z

data Snoc c x y where
  Begin :: Snoc c x x
  Snoc :: Snoc c x y -> c y z -> Snoc c x z

class Maps phi where -- laws like Functor
  maps :: (forall x y . p x y -> q x y) -> phi p a b -> phi q a b 

instance Maps Cons where
  maps phi Nil = Nil
  maps phi (Cons a bs) = Cons (phi a) (maps phi bs)
  {-# INLINABLE maps #-}
  
instance Maps Snoc where
  maps phi Begin = Begin
  maps phi (Snoc bs a) = Snoc (maps phi bs)  (phi a)
  {-# INLINABLE maps #-}
  
-- for the generalized Sequence class we need specialized
-- viewr / viewl types to keep a parameter 'hidden':
data UnCons s c x y where
   Empty  :: UnCons s c x x
   (:|)     :: c x y -> s c y z -> UnCons s c x z

data UnSnoc s c x y where
   NoSnoc  :: UnSnoc s c x x
   (:|<)     :: s c x y -> c y z -> UnSnoc s c x z


class Sequence s where
  -- minimal complete def: blank, singleton, (uncons or unsnoc) and (><) or (|>) or (<|)
  blank     :: s c x x
  singleton  :: c x y -> s c x y
  (><)       :: s c x y -> s c y z  -> s c x z
  uncons       :: s c x y -> UnCons s c x y
  unsnoc      :: s c x y -> UnSnoc s c x y
  (|>)       :: s c x y -> c y z -> s c x z
  (<|)       :: c x y -> s c y z -> s c x z
  
  l |> r = l >< singleton r
  l <| r = singleton l >< r
  l >< r = case uncons l of
    Empty -> r
    h :| t  -> h <| (t >< r)

  uncons q = case unsnoc q of 
    NoSnoc -> Empty
    p :|< l -> case uncons p of
        Empty -> l :| blank
        h :| t ->  h :| (t |> l)

  unsnoc q = case uncons q of 
    Empty -> NoSnoc
    h :| t -> case unsnoc t of
        NoSnoc -> blank :|< h
        p :|< l ->  (h <| p) :|< l

instance Sequence Snoc where
  blank = Begin
  {-# INLINE blank #-}
  singleton c = Snoc Begin c 
  {-# INLINE singleton #-}
  (|>) = Snoc
  {-# INLINE (|>) #-}
  unsnoc Begin = NoSnoc
  unsnoc (Snoc p l) = p :|< l
  {-# INLINE unsnoc #-}

instance Sequence Cons where
  blank = Nil
  {-# INLINE blank #-}
  singleton c = Cons c Nil
  {-# INLINE singleton #-}
  (<|) = Cons
  {-# INLINE (<|) #-}
  uncons Nil = Empty
  uncons (Cons h t) = h :| t
  {-# INLINE uncons #-}
