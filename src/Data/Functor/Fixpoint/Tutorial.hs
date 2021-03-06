{-# LANGUAGE TemplateHaskell, DeriveFunctor, TypeFamilies #-}
{-# LANGuaGE FlexibleContexts, UndecidableInstances #-}

module Data.Functor.Fixpoint.Tutorial where

import Data.Functor.Fixpoint

-----------------------------------------------------------------
--   Creating F-algebras from recursive types
-----------------------------------------------------------------


-- Example #1 --

data Ast
  = Add Ast Ast
  | Mul Ast Ast
  | Number Integer
  deriving (Show)

-- Create the F-algebra AstF and related recursion-schemes machinery.
makeAlgebra ''Ast




-- Example #2 --

data Tree a = Leaf a | Fork (Tree a) (Tree a)

-- Create the F-algebra TreeF and related recursion-schemes machinery.
makeAlgebra ''Tree



-----------------------------------------------------------------
--   Creating F-algebra and fixpoint transformers from functors
-----------------------------------------------------------------

data HoleyF t = HoleF | ExistingF t deriving Functor

-- Create the F-algebra transformer HoleyT and the fixpoint transformer Holey.
makeTransformer ''HoleyF



-----------------------------------------------------------------
--   Composable functions on recursive types (IN PROGRESS)
-----------------------------------------------------------------

-- Example #1

-- Define an instance directly on the recursive type
instance Show a => Show (Tree a) where
  show (Leaf x) = show x
  show (Fork l r) = "(" ++ show l ++ " " ++ show r ++ ")"

-- Splice in an instance of Show for TreeF, based on the
-- instance for Tree. (TODO)
aLaCarte ''Tree ''Show

-- The spliced instance should look something like this:
instance (Show a, Show t) => Show (TreeF a t) where
  show (LeafF x) = show x
  show (ForkF l r) = "(" ++ show l ++ " " ++ show r ++ ")"

-- Example #2

-- Define an instance for a transformer's underlying functor:
instance Show t => Show (HoleyF t) where
  show HoleF = "_"
  show (ExistingF x) = show x

-- Splice in an instance for HoleyF and for Holey (TODO)
aLaCarteT ''HoleyT ''Show

-- The spliced instance for HoleyF should look something like this:
instance Show (f t) => Show (HoleyT f t) where
  show x = show $ case x of
    HoleT       -> HoleF
    ExistingT e -> ExistingF e

-- The spliced instance for Holey should look something like this:
instance (Recursive t, Show (Base t (Holey t))) => Show (Holey t) where
  show = show . project

-----------------------------------------------------------------
--   Usage examples
-----------------------------------------------------------------

tree :: Tree Int
tree = Fork (Fork (Leaf 1) (Leaf 2)) (Fork (Fork (Leaf 3) (Leaf 4)) (Leaf 5))

punch :: (Recursive t, Corecursive t) => (t -> Bool) -> t -> Holey t
punch test = unfold phi
  where
    phi x = if test x then HoleT else ExistingT (project x)

-- λ> show tree
--
--
