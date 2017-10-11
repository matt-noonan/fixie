{-# LANGUAGE TemplateHaskell, DeriveFunctor, TypeFamilies #-}
{-# LANGuaGE FlexibleContexts, UndecidableInstances #-}

module Data.Functor.Fixpoint.Tutorial where

import Data.Functor.Fixpoint

data Ast
  = Add Ast Ast
  | Mul Ast Ast
  | Number Integer
  deriving (Show)


makeAlgebra ''Ast

data Tree a = Leaf a | Fork (Tree a) (Tree a)

makeAlgebra ''Tree

instance Show a => Show (Tree a) where
  show (Leaf x) = show x
  show (Fork l r) = "(" ++ show l ++ " " ++ show r ++ ")"

instance (Show a, Show t) => Show (TreeF a t) where
  show (LeafF x) = show x
  show (ForkF l r) = "(" ++ show l ++ " " ++ show r ++ ")"

aLaCarte ''Tree ''Show

data HoleyF t = HoleF | ExistingF t deriving Functor

makeTransformer ''HoleyF

aLaCarteT ''HoleyT ''Show

instance Show t => Show (HoleyF t) where
  show HoleF = "_"
  show (ExistingF x) = show x

instance (Recursive t, Show (Base t (Holey t))) => Show (Holey t) where
  show = show . project

--------------------------------------------------------------
--   Usage examples
--------------------------------------------------------------


tree :: Tree Int
tree = Fork (Fork (Leaf 1) (Leaf 2)) (Fork (Fork (Leaf 3) (Leaf 4)) (Leaf 5))

punch :: (Recursive t, Corecursive t) => (t -> Bool) -> t -> Holey t
punch test = unfold phi
  where
    phi x = if test x then HoleT else ExistingT (project x)

