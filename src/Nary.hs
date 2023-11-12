module Nary where

class Nary t a b where
  nary :: t -> [a] -> Maybe b

instance Nary b a b where
  nary :: b -> [a] -> Maybe b
  nary v [] = Just v
  nary _ (_ : _) = Nothing

instance (Nary t a b) => Nary (a -> t) a b where
  nary f (arg : rest) = nary (f arg) rest
  nary _ [] = Nothing

instance Nary (Maybe a -> b) a b where
  nary f [] = Just $ f Nothing
  nary f [a] = Just $ f (Just a)
  nary _ (_ : _ : _) = Nothing

instance Nary ([a] -> b) a b where
  nary = fmap Just