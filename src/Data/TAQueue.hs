{-# LANGUAGE GADTs #-}

-- | A type-aligned queue.
module Data.TAQueue where

data TAQueue f a b where
  Leaf :: (a -> f b) -> TAQueue f a b
  Node :: TAQueue f a x -> TAQueue f x b -> TAQueue f a b

{-# INLINE singleton #-}
singleton :: (a -> f b) -> TAQueue f a b
singleton = Leaf

{-# INLINE snoc #-}
snoc :: TAQueue f a x -> (x -> f b) -> TAQueue f a b
snoc t r = Node t (Leaf r)

{-# INLINE append #-}
append :: TAQueue f a x -> TAQueue f x b -> TAQueue f a b
append t1 t2 = Node t1 t2

data ViewL f a b where
  Singleton :: (a -> f b) -> ViewL f a b
  Cons      :: (a -> f x) -> TAQueue f x b -> ViewL f a b

viewl :: TAQueue f a b -> ViewL f a b
viewl (Leaf r)     = Singleton r
viewl (Node t1 t2) = go t1 t2
 where
   go :: TAQueue f a x -> TAQueue f x b -> ViewL f a b
   go (Leaf r)       tr = Cons r tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
