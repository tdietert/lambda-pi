{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module LambdaPi
  ()
where

import           Control.Monad                    (unless)
import           Control.Monad.Except             (MonadError, throwError)
import           Data.Coerce                      (coerce)
import           Data.Map                         (Map, insert, lookup)
import           Data.String                      (IsString)
import           GHC.Generics                     (Generic)
import           Prelude                          hiding (lookup)
import           Unbound.Generics.LocallyNameless

import           Debug.Trace                      (traceM)
import           GHC.Stack                        (HasCallStack, callStack)

type Var = Name Syn

-- | Type-inferable terms
--
-- Somtimes called "synthesized" terms
--
data Syn
  = Var Var -- ^ Free and bound variables
  | Ann Chk Chk -- ^ Annoted terms
  | App Syn Chk -- ^ Application
  | Pi Chk (Bind Var Chk) -- ^ The term for arrow types
  | Star -- ^ The term for kinds of types
  deriving (Show, Generic)

instance Alpha Syn

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

instance Subst Chk Syn
instance Subst Chk Chk

type VVar = Name Value

data Value
  = VLam (Bind VVar Value) -- ^ A lambda abstraction value
  | VStar -- ^ The evaluated type of 'Star'
  | VPi Value (Bind VVar Value) -- ^ A type abstraction value
  | VFree VVar -- ^ A free variable, "neutral" term
  | VApp Value Value -- ^ A value application to another value, "neutral" term
  deriving (Show, Generic)

instance Alpha Value
instance Subst Value Value where
  isvar (VFree x) = Just (SubstName x)
  isvar _         = Nothing

type Env = Map VVar Value
type Result = Either [Char]

eval :: Syn -> Result Value
eval = runFreshMT . evalSyn

-- | Evaluation of terms
--
-- We must write an evaluator as types can now depend on values
--
evalSyn :: Syn -> FreshMT Result Value
evalSyn syn = case syn of
  Var x    -> pure $ VFree (coerce x)
  Ann e _  -> evalChk e
  App e e' -> do
    v <- evalSyn e
    case v of
      VLam binder -> do
        (x, body) <- unbind binder
        pure (subst x v body)
      _ -> throwError "invalid apply"
  Star    -> pure VStar
  -- Is this correct?
  Pi p p' -> do
    t      <- evalChk p
    (x, e) <- unbind p'
    t'     <- evalChk e
    pure $ VPi t (bind (coerce x) t')

evalChk :: Chk -> FreshMT Result Value
evalChk chk = case chk of
  Inf syn    -> evalSyn syn
  Lam binder -> do
    (x, e) <- unbind binder
    e'     <- evalChk e
    pure $ VLam (bind (coerce x) e')

-- We store types in their evaluated form
type Type = Value
type Context = Map VVar Type

typecheck :: HasCallStack => Syn -> Result Type
typecheck = runFreshMT . typeSyn mempty
 where
  -- Types that should be synthesized
  typeSyn :: HasCallStack => Context -> Syn -> FreshMT Result Type
  typeSyn ctx syn = case syn of
    Var x -> case lookup (coerce x) ctx of
      Nothing -> do
        traceM (show callStack)
        throwError "unknown identifier"
      Just t -> pure t
    Ann e p -> do
      typeChk ctx p VStar
      t <- evalChk p
      traceM (show t)
      typeChk ctx e t
      pure t
    App e e' -> do
      sigma <- typeSyn ctx e
      case sigma of
        VPi t t' -> do
          typeChk ctx e' t
          (x, body) <- unbind t'
          v         <- evalChk e'
          pure (subst x v body)
        _ -> throwError "illegal application"
    Star    -> pure VStar
    Pi p p' -> do
      typeChk ctx p VStar
      t      <- evalChk p
      (x, e) <- unbind p'
      let x' = coerce x
      traceM (show x')
      typeChk (insert x' t ctx) e VStar
      pure VStar

  -- Types that should be "checked"
  typeChk :: HasCallStack => Context -> Chk -> Type -> FreshMT Result ()
  typeChk ctx chk v = case chk of
    Inf e -> do
      v' <- typeSyn ctx e
      unless (aeq v v') $ throwError "type mismatch syn"
    Lam binder -> case v of
      VPi t p' -> do
        -- here, the variable names are assumed to be the same,
        -- thus we only use the 'x' unbound from p'
        (_, e ) <- unbind binder
        (x, t') <- unbind p'
        typeChk (insert x t ctx) e t'
      v -> do
        traceM (show v)
        traceM (show callStack)
        throwError "type mismatch lam"

----------------------------------------
-- Test
----------------------------------------

var = Var . s2n
syn = Inf
synvar = syn . var

lambda x = Lam . bind (s2n x)
pi' v t t' = syn $ Pi t (bind (s2n v) t')

id' = lambda "x" (syn (var "x"))
const' = lambda "x" . lambda "y" . syn $ var "x"

annConst' = Ann
  const'
  (pi' "x"
       (pi' "y" (synvar "b") (synvar "b"))
       (pi' "z" (synvar "a") (pi' "w" (synvar "b") (synvar "b")))
  )

(<|) :: Syn -> Chk -> Syn
(<|) f x = App f x
