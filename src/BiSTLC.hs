{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE StandaloneDeriving         #-}

module BiSTLC
  ()
where

import           Control.Monad                    (unless)
import           Control.Monad.Except             (MonadError, throwError)
import           Data.Map                         (Map, insert, lookup)
import           Data.String                      (IsString)
import           GHC.Generics                     (Generic)
import           Prelude                          hiding (lookup)
import           Unbound.Generics.LocallyNameless

type Var = Name Syn

-- | Type-inferable terms
--
-- Somtimes called "synthesized" terms
--
data Syn
  = Var Var -- ^ Free and bound variables
  | Ann Chk Type -- ^ Annoted terms
  | App Syn Chk -- ^ Application
  deriving (Show, Generic)

instance Alpha Syn

instance Subst Syn Type
instance Subst Syn Chk
instance Subst Syn Syn where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

-- | Type-checkable Terms
--
-- Sometimes called "checked" terms
--
data Chk
  = Inf Syn -- ^ Inferable terms embedded in checkable terms
  | Lam (Bind Var Chk) -- ^ Lambda term
  deriving (Show, Generic)

instance Alpha Chk

data Type
  = TFree Var -- ^ Free type variables
  | Type :-> Type -- ^ The type of lambda abstractions
  deriving (Show, Eq, Generic)

instance Alpha Type

data Kind
  = Star
  deriving (Show, Eq)

data TypeInfo
  = HasKind Kind
  | HasType Type
  deriving (Show, Eq)

type Context = Map Var TypeInfo
type Result = Either [Char]

-- | Assert that a given type is of a given kind
kind :: MonadError [Char] m => Context -> Type -> Kind -> m ()
kind ctx typ k = case (typ, k) of
  (TFree x, Star) -> case lookup x ctx of
    Nothing             -> throwError "unknown identifier"
    Just (HasType _   ) -> throwError "type should have kind"
    Just (HasKind Star) -> pure ()
  (tau :-> tau', Star) -> do
    kind ctx tau  Star
    kind ctx tau' Star

typecheck :: Context -> Syn -> Result Type
typecheck ctx' = runFreshMT . typeSyn ctx'
 where
  -- Types that should be synthesized
  typeSyn :: Context -> Syn -> FreshMT Result Type
  typeSyn ctx syn = case syn of
    Var x -> case lookup x ctx of
      Nothing          -> throwError "unknown identifier"
      Just (HasKind _) -> throwError "var should have type, not kind"
      Just (HasType t) -> pure t
    Ann e t -> do
      kind ctx t Star
      typeChk ctx e t
      pure t
    App e e' -> do
      sig <- typeSyn ctx e
      case sig of
        t :-> t' -> do
          typeChk ctx e' t
          pure t'
        _ -> throwError "illegal application"

  -- Types that should be "checked"
  typeChk :: Context -> Chk -> Type -> FreshMT Result ()
  typeChk ctx chk t = case chk of
    Inf e -> do
      t' <- typeSyn ctx e
      unless (t == t') (throwError "type mismatch")
    Lam binder -> case t of
      t' :-> t'' -> do
        -- Here we simply "unbind" the expression to get a globally fresh
        -- variable 'x', and continue typechecking the body of the lambda
        (x, body) <- unbind binder
        typeChk (insert x (HasType t') ctx) body t''
      _ -> throwError "type mismatch"
