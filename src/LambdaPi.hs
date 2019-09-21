{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}

module LambdaPi
where

import Control.Monad                    (unless)
import Control.Monad.Except             (MonadError, throwError)
import Data.Coerce                      (coerce)
import Data.Map                         (Map, insert, lookup)
import Data.String                      (IsString)
import Data.Typeable                    (Typeable)
import Debug.Trace                      (traceM)
import GHC.Exts                         (toList)
import GHC.Generics                     (Generic)
import GHC.Stack                        (HasCallStack, callStack)
import Prelude                          hiding (lookup, pi)

import Unbound.Generics.LocallyNameless

-- | Variables for Syn expressions
type Var = Name Syn

-- | Type synonym to leverage instances for 'Rebind'
type UniTele expr = Rebind (Name Syn, Embed expr) ()
type Rebindable expr = (Typeable expr, Alpha expr)

mkUniTele :: Rebindable expr => [Char] -> expr -> UniTele expr
mkUniTele x e = rebind (s2n x, Embed e) ()

-- | Type-inferable (synthesizable) terms
data Syn
  = Var Var -- ^ Free and bound variables
  | Ann Chk Chk -- ^ Annoted terms
  | App Syn Chk -- ^ Application
  | Pi (Bind (UniTele Chk) Chk)-- ^ The term for arrow types
  | Star -- ^ The term for kinds of types
  deriving (Show, Generic)

instance Alpha Syn

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
instance Subst Syn Chk where
  isCoerceVar (Inf (Var x)) = Just (SubstCoerce x (Just . Inf))
  isCoerceVar _ = Nothing

type VVar = Name Value

type VUniTele = Rebind (VVar, Embed Value) ()

data Value
  = VLam (Bind VVar Value) -- ^ A lam abstraction value
  | VStar -- ^ The evaluated type of 'Star'
  | VPi (Bind VUniTele Value) -- ^ A type abstraction value
  | VVar VVar -- ^ A free variable, "neutral" term
  | VApp Value Value -- ^ A value application to another value, "neutral" term
  deriving (Show, Generic)

instance Alpha Value
instance Subst Value Value where
  isvar (VVar x) = Just (SubstName x)
  isvar _         = Nothing

type Env = Map VVar Value
type Result = Either [Char]

type TypecheckM a = FreshMT Result a

throwErrorTypecheckM :: (HasCallStack, MonadError e m) => e -> m a
throwErrorTypecheckM err = do
  mapM_ (traceM . show) (toList callStack)
  throwError err

eval :: Syn -> Result Value
eval = runFreshMT . evalSyn

-- | Evaluation of terms
--
-- We must write an evaluator as types can now depend on values
--
evalSyn :: Syn -> TypecheckM Value
evalSyn syn = case syn of
  Var x -> let vx = coerce x in pure (VVar vx)
  Ann e _ -> evalChk e
  App e e' -> do
    ve <- evalSyn e
    ve' <- evalChk e'
    case ve of
      VLam binder -> do
        (x, body) <- unbind binder
        pure (subst x ve' body)
      -- This case embodies a "free" function name in the context
      VVar x -> pure $ VApp (VVar x) ve'
      _ -> throwErrorTypecheckM "invalid apply"
  Star -> pure VStar
  Pi binding -> do
    (xp, p') <- unbind binding
    let ((x, Embed p),()) = unrebind xp
        vx = coerce x
    t <- evalChk p
    t' <- evalChk p'
    let xt = rebind (vx, Embed t) ()
    pure $ VPi (bind xt t')


-- | Evaluate a checkable expression
evalChk :: Chk -> TypecheckM Value
evalChk chk = case chk of
  Inf syn -> evalSyn syn
  Lam binding -> do
    (x, e) <- unbind binding
    ve <- evalChk e
    pure $ VLam (bind (coerce x) ve)

-- We store types in their evaluated form
type Type = Value
type Context = Map VVar Type

-- | Typecheck an expression whose type is synthesizable
typecheck :: HasCallStack => Syn -> Result Type
typecheck = runFreshMT . typeSyn mempty

-- | Types that should be synthesized
typeSyn :: HasCallStack => Context -> Syn -> TypecheckM Type
typeSyn ctx syn = case syn of
  Var x -> case lookup (coerce x) ctx of
    Nothing -> throwErrorTypecheckM ("unknown identifier: " ++ show x)
    Just t -> pure t
  Ann e p -> do
    typeChk ctx p VStar
    t <- evalChk p
    typeChk ctx e t
    pure t
  App e e' -> do
    sigma <- typeSyn ctx e
    case sigma of
      VPi binding -> do
        (xt, t') <- unbind binding
        let ((x, Embed t), ()) = unrebind xt
        typeChk ctx e' t
        ve' <- evalChk e'
        pure (subst (coerce x) ve' t')
      _ -> throwErrorTypecheckM "illegal application"
  Star    -> pure VStar
  Pi xp_p' -> do
    (xp, p') <- unbind xp_p'
    let ((x,Embed p), ()) = unrebind xp
    typeChk ctx p VStar
    t <- evalChk p
    typeChk (insert (coerce x) t ctx) p' VStar
    pure VStar

-- Types that should be "checked"
typeChk :: HasCallStack => Context -> Chk -> Type -> TypecheckM ()
typeChk ctx chk v = case chk of
  Inf e -> do
    v' <- typeSyn ctx e
    unless (aeq v v') $
      throwErrorTypecheckM "type mismatch syn"
  Lam x_e -> case v of
    VPi xt_t'-> do
      (x , e) <- unbind x_e
      (xt, t') <- unbind xt_t'
      let ((_,Embed t),_) = unrebind xt
      typeChk (insert (coerce x) t ctx) e t'
    v -> throwErrorTypecheckM ("type mismatch lam: " ++ show v)

----------------------------------------
-- DSL for term easier construction
----------------------------------------

syn = Inf
var = syn . Var . s2n

lam x = Lam . bind (s2n x)
pi' x t t' = syn $ Pi (bind (mkUniTele x t) t')

id' = lam "x" (var "x")
const' = lam "x" (lam "y" (var "x"))

annConst' = Ann
  const'
  (pi' "x"
       (pi' "y" (var "b") (var "b"))
       (pi' "z" (var "a") (pi' "w" (var "b") (var "b")))
  )

ann :: Chk -> Chk -> Syn
ann e t = Ann e t

(<|) :: Syn -> Chk -> Syn
(<|) f x = App f x
