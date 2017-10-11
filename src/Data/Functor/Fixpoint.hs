{-# LANGUAGE TemplateHaskell, QuasiQuotes, LambdaCase, TupleSections #-}

module Data.Functor.Fixpoint
       ( makeAlgebra
       , aLaCarte
       , makeTransformer
       , aLaCarteT
       , module Data.Functor.Foldable
       , module Language.Haskell.TH
       , module Language.Haskell.TH.Syntax
       )
       where

import Data.Functor.Foldable

import Data.List
import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- | Given a recursive data type, generate the underlying F-algebra
-- along with a type family instance for @Base@ and instances for
-- @Recursive@ and @Corecursive@.
--
-- @makeAlgebra@ enables you to write a recursive type directly,
-- and then auto-generate all of the machinery needed to make use
-- of generic recursion schemes.
makeAlgebra :: Name -> Q [Dec]
makeAlgebra name = do

  Just ty <- lookupTypeName (show name)
  TyConI dec <- reify ty

  tyVar <- newName "t"

  case dec of
    DataD ctx tyCtor binders kind con _ -> do

      let binderTyVar = VarT . \case
            PlainTV n    -> n
            KindedTV n _ -> n

          baseTy  = foldl' AppT (ConT tyCtor) (map binderTyVar binders)
          baseFTy = foldl' AppT (ConT $ addF tyCtor) (map binderTyVar binders)


          map2 f = map (\(x,y) -> (x, f y))

          deriv = [ConT (mkName "Functor")]

      let ctorF = \case
            NormalC n args -> NormalC (addF n) (map2 (replaceTy baseTy (VarT tyVar)) args)
            _ -> error "Expected only normal constructors!"

      proj <- mkProjEmbd "project" id addF con
      embd <- mkProjEmbd "embed"   addF id con
      
      return [ -- The F-algebra.
               DataD ctx (addF name)
                     (binders ++ [PlainTV tyVar])
                     kind
                     (map ctorF con) deriv
                     
               -- The 'Base' type family instance for recursion-schemes.
             , TySynInstD (mkName "Base") (TySynEqn [baseTy] baseFTy)

               -- The 'Recursive' instance.
             , InstanceD Nothing []
                 (AppT (ConT $ mkName "Recursive") baseTy) [proj]

               -- The 'Corecursive' instance.
             , InstanceD Nothing []
                 (AppT (ConT $ mkName "Corecursive") baseTy) [embd]
             ]
      
    _ -> error ("Expecting " ++ show name ++ " to be a 'data' declaration!")

-- | Add an @F@ suffix to a @Name@.
addF :: Name -> Name
addF n = mkName (nameBase n ++ "F")

-- | Remove an @F@ suffix to a @Name@, or die trying.
unF :: Name -> Name
unF n = case last (nameBase n) of
  'F' -> mkName (init $ nameBase n)
  _   -> error ("Expected " ++ show n ++ " to end with an 'F'.")

-- | Convert an @F@ suffix to a @T@ suffix.
cvtF2T :: Name -> Name
cvtF2T n = mkName (nameBase (unF n) ++ "T")

-- | Substitute one type for another in a @Type@.
replaceTy :: Type -> Type -> Type -> Type
replaceTy from to ty = let go = replaceTy from to in
  if ty == from
  then to
  else case ty of
    AppT    h t   -> AppT    (go h) (go t)
    InfixT  l n r -> InfixT  (go l) n (go r)
    UInfixT l n r -> UInfixT (go l) n (go r)
    ParensT x     -> ParensT (go x)
    _             -> ty

-- | Generate the body for a @Recursive@ or @Corecursive@ instance.
mkProjEmbd :: String -> (Name -> Name) -> (Name -> Name) -> [Con] -> Q Dec
mkProjEmbd n renameL renameR ctors = (FunD (mkName n)) <$> mapM clause ctors
  where
    clause (NormalC name btypes) = do
      tvs <- replicateM (length btypes) (newName "x")
      return $ Clause [ConP (renameL name) $ map VarP tvs]
                      (NormalB $ foldl' AppE (ConE (renameR name)) (map VarE tvs)) []

-- | Lift a typeclass instance defined on a fixpoint type @Fxpt@ back
-- to an equivalent instance on the underlying F-algebra @FxptT@.
aLaCarte :: Name -> Name -> Q [Dec]
aLaCarte name tclass = do
  runIO (putStrLn "TODO: aLaCarte")
  return []

-- | Make an F-algebra transformer out of a functor.
-- This works by using a functor @FunF t@ to generate a new
-- type @FunF f t@. Every appearance of @t@ in @FunT@
-- becomes @(f t)@ in @FunF@. We derive @Functor@ on @FunT@
-- so that whenever @f@ is a @Functor@, so is @FunF f@.
--
-- Finally, we generate a type @Fun f@ isomorphic to
-- the fixpoint of @FunF f@. When @f@ is an instance of
-- @Recursive@ or @Corecursive@, @Fun f@ will be as well.
makeTransformer :: Name -> Q [Dec]
makeTransformer name = do

  Just ty <- lookupTypeName (show name)
  TyConI dec <- reify ty

  tyVar1 <- newName "f"
  tyVar2 <- newName "t"

  fixpt <- newName "fixpt"
  
  case dec of
    DataD ctx tyCtor binders kind con _ -> do

      let binderTyVar = VarT . \case
            PlainTV n    -> n
            KindedTV n _ -> n

          baseTy  = binderTyVar lastBinder
          baseUnFTy = foldl' AppT (ConT $ unF tyCtor)
                             (map binderTyVar binders' ++ [VarT fixpt])

          unrolled = AppT (foldl' AppT (ConT $ cvtF2T tyCtor) (map binderTyVar binders'))
                          (AppT (ConT $ mkName "Base")
                                (VarT fixpt))
          
          baseless = AppT (AppT (ConT $ mkName "Base") (VarT tyVar1))
                          (AppT (ConT $ unF ty) (VarT tyVar1))
            
          map2 f = map (\(x,y) -> (x, f y))

          deriv = [ConT (mkName "Functor")]

          lastBinder = last binders
          binders' = init binders
      
      let ctorF = \case
            NormalC n args -> NormalC (cvtF2T n)
                                      (map2 (replaceTy baseTy
                                                       (AppT (VarT tyVar1)
                                                             (VarT tyVar2)))
                                             args)
            _ -> error "Expected only normal constructors!"
            
          ctor = \case
            NormalC n args -> NormalC (unF n)
                                      (map2 (replaceTy baseTy baseless) args)
            _ -> error "Expected only normal constructors!"
            
      proj <- mkProjEmbd "project" unF cvtF2T con
      embd <- mkProjEmbd "embed"   cvtF2T unF con

      return [ -- The F-algebra transformer.
               DataD ctx (cvtF2T name)
                     (binders' ++ [PlainTV tyVar1, PlainTV tyVar2])
                     kind
                     (map ctorF con) deriv

               -- The fixpoint-of-composition operator.
             , DataD ctx (unF name)
                     (binders' ++ [PlainTV tyVar1])
                     kind
                     (map ctor con) []
                     
               -- The 'Base' type family instance for recursion-schemes.
             , TySynInstD (mkName "Base")
                          (TySynEqn [baseUnFTy] unrolled)

               -- Inherited Recursive instances.
             , InstanceD Nothing [AppT (ConT $ mkName "Recursive") (VarT fixpt)]
               (AppT (ConT $ mkName "Recursive") (AppT (ConT $ unF tyCtor) (VarT fixpt))) [proj]
 
               -- Inherited Corecursive instances.
             , InstanceD Nothing [AppT (ConT $ mkName "Corecursive") (VarT fixpt)]
               (AppT (ConT $ mkName "Corecursive") (AppT (ConT $ unF tyCtor) (VarT fixpt))) [embd]
 
             ]
      
    _ -> error ("Expecting " ++ show name ++ " to be a 'data' declaration!")

-- | Lift a typeclass instance defined on a functor @FunF@
-- to an equivalent instance on the F-algebra transformer @FunT@
-- and @Fun@.
aLaCarteT :: Name -> Name -> Q [Dec]
aLaCarteT name tclass = do
  runIO (putStrLn "TODO: aLaCarteT")
  return []
