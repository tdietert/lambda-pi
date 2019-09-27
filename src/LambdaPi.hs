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

import Control.Monad                    ((<=<), unless)
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
import Text.PrettyPrint                 (Doc, (<+>), brackets, char, colon, parens, text)

import Unbound.Generics.LocallyNameless

----------------------------------------
--  Lambda-Pi Terms
----------------------------------------

-- | Variables for Type-synthesizable expressions
type Var = Name Syn

-- | Type synonym, leveraging instances for 'Rebind'
type UniTele expr = Rebind (Var, Embed expr) ()
type Rebindable expr = (Typeable expr, Alpha expr)

-- | Smart constructor for the UniTele type
mkUniTele :: Rebindable expr => [Char] -> expr -> UniTele expr
mkUniTele x e = rebind (s2n x, Embed e) ()

-- | Type-inferable (synthesizable) terms
data Syn
  = Var Var -- ^ Free and bound variables
  | Ann Chk Chk -- ^ Annoted terms
  | App Syn Chk -- ^ Application
  | Pi (Bind (UniTele Chk) Chk)-- ^ The term for arrow types
  | Star -- ^ The term for kinds of types
  -- Natural Numbers
  | Nat -- Type of natural numbers
  | NatElim Chk Chk Chk Chk -- Natural number eliminator*
  | Zero -- Natural number '0'
  | Succ Chk -- Successor of Nat
  deriving (Show, Generic)

instance Alpha Syn

instance Subst Syn Syn where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

-- | Terms whose types must be checked (we cannot infer them via context)
data Chk
  = Inf Syn -- ^ Inferable terms embedded in checkable terms
  | Lam (Bind Var Chk) -- ^ Lambda term
  deriving (Show, Generic)

instance Alpha Chk
instance Subst Chk Syn
instance Subst Chk Chk
-- We must tell unbound-generics how to rebuild the Chk expr after digging in
-- and substituting the variable.
instance Subst Syn Chk where
  isCoerceVar (Inf (Var x)) = Just (SubstCoerce x (Just . Inf))
  isCoerceVar _ = Nothing

----------------------------------------
-- Values
----------------------------------------

type VVar = Name Value
type VUniTele = Rebind (VVar, Embed Value) ()

mkVUniTele :: [Char] -> Value -> VUniTele
mkVUniTele x e = rebind (s2n x, Embed e) ()

data Value
  = VLam (Bind VVar Value) -- ^ A lam abstraction value
  | VStar -- ^ The evaluated type of 'Star'
  | VPi (Bind VUniTele Value) -- ^ A type abstraction value
  | VVar VVar -- ^ A free variable, "neutral" term
  | VApp Value Value -- ^ A value application to another value, "neutral" term
  -- [WIP] Natural Number values
  | VNat
  | VZero
  | VSucc Value
  | VNatElim Value Value Value Value
  deriving (Show, Generic)

instance Alpha Value
instance Subst Value Value where
  isvar (VVar x) = Just (SubstName x)
  isvar _         = Nothing

----------------------------------------
-- Evaluation & Typechecking
----------------------------------------

type Env = Map VVar Value
type Result = Either [Char]

type TypecheckM a = FreshMT Result a

throwErrorTypecheckM :: (HasCallStack, MonadError e m) => e -> m a
throwErrorTypecheckM err = do
  mapM_ (traceM . show) (reverse $ toList callStack)
  throwError err

eval :: Syn -> Result Value
eval = runFreshMT . evalSyn

-- | Evaluation of terms
--
-- We must write an evaluator as types can now depend on values, and in order to
-- "compute the type" of a type, we must sometimes evaluate the "type expression"
--
evalSyn :: HasCallStack => Syn -> TypecheckM Value
evalSyn syn = case syn of
  Var x -> let vx = coerce x in pure (VVar vx)
  Ann e _ -> evalChk e
  App e e' -> do
    ve <- evalSyn e
    ve' <- evalChk e'
    vapp ve ve'
  Star -> pure VStar
  Pi binding -> do
    (xp, p') <- unbind binding
    let ((x, Embed p),()) = unrebind xp
        vx = coerce x
    t <- evalChk p
    t' <- evalChk p'
    let xt = rebind (vx, Embed t) ()
    pure $ VPi (bind xt t')

  -- [WIP] Evaluation of Natural Numbers
  Nat -> pure VNat
  Zero -> pure VZero
  Succ k -> pure . VSucc =<< evalChk k
  NatElim m mz ms k -> do
    vk <- evalChk k
    case vk of
      VZero -> evalChk mz
      VSucc l -> do
        vm <- evalChk m
        vmz <- evalChk mz
        vms <- evalChk ms
        let rec = VNatElim vm vmz vms l
        vmsl <- vapp vms l
        vapp vmsl rec
      -- TODO "Neutral" term for VNatElim?
      VVar x -> do
        vm <- evalChk m
        vmz <- evalChk mz
        vms <- evalChk ms
        pure (VNatElim vm vmz vms (VVar x))
      _ -> throwErrorTypecheckM "evalSyn: NatElim"

-- | Helper function for value application
vapp :: HasCallStack => Value -> Value -> TypecheckM Value
vapp ve ve' =
  case ve of
    VLam binder -> do
      (x, body) <- unbind binder
      pure (subst x ve' body)
    -- This case embodies a "free" function name in the context
    VVar x -> pure $ VApp (VVar x) ve'
    _ -> throwErrorTypecheckM "invalid apply"

-- | Evaluate a checkable expression
evalChk :: HasCallStack => Chk -> TypecheckM Value
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

typecheckPretty :: HasCallStack => Syn -> Result Doc
typecheckPretty = runFreshMT . (ppr <=< typeSyn mempty)

-- | Compute the type of a term whose type can be synthesized given a context
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
  -- [WIP] Type "synthesis" of Natural number terms
  Nat -> pure VStar
  Zero -> pure VNat
  Succ k -> do
    typeChk ctx k VNat
    pure VNat
  NatElim m mz ms k -> do
    typeChk ctx m (tarr VNat VStar)
    vm <- evalChk m
    typeChk ctx mz =<< vapp vm VZero
    vk <- evalChk k
    vmk <- vapp vm vk
    typeChk ctx ms =<<
      pure . VPi . bind (mkVUniTele "l" VNat) . tarr vmk =<<
        vapp vm (VSucc (VVar (s2n "l")))
    typeChk mempty k VNat
    pure vmk

tarr :: Type -> Type -> Type
tarr a b = VPi (bind (mkVUniTele "_" a) b)

-- | Check the type of a given type-checkable term
typeChk :: HasCallStack => Context -> Chk -> Type -> TypecheckM ()
typeChk ctx chk v = case chk of
  Inf e -> do
    v' <- typeSyn ctx e
    unless (aeq v v') $
      throwErrorTypecheckM $ unlines
        [ "type mismatch syn:"
        , "  expected: "++ show v
        , "  but got: " ++ show v'
        ]

  Lam x_e -> case v of
    VPi xt_t'-> do
      (x , e) <- unbind x_e
      (xt, t') <- unbind xt_t'
      let ((_,Embed t),_) = unrebind xt
      typeChk (insert (coerce x) t ctx) e t'
    _ -> throwErrorTypecheckM ("type mismatch lam: " ++ show v)

----------------------------------------
-- DSL for term easier construction
----------------------------------------

chk = Inf
svar = Var . s2n
var = chk . svar

lam x = Lam . bind (s2n x)
pi' x t t' = chk $ Pi (bind (mkUniTele x t) t')

id' = lam "a" $ lam "x" (var "x")
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

plus =
   NatElim
     (lam "_" (pi' "_" (Inf Nat) (Inf Nat)))
     (lam "n" (var "n"))
     (lam "k" (lam "rec" (lam "n" (chk (Succ (chk (App (svar "rec") (var "n"))))))))

----------------------------------------
-- Pretty Printer
----------------------------------------

class Pretty a where
  ppr :: (Applicative m, Fresh m) => a -> m Doc

instance Pretty Syn where
  ppr (Var x) = pure (pprNameLocal x)
  ppr (App e e') = (<+>) <$> ppr e <*> (parens <$> ppr e')
  ppr (Ann e t) = do
    pe <- ppr e
    pt <- ppr t
    pure (parens pe <+> colon <+> pt)
  ppr Star = pure (char '*')
  ppr (Pi xt_t) = do
    (xt, e) <- unbind xt_t
    pe <- ppr e
    let ((x, Embed t), ()) = unrebind xt
    pt <- ppr t
    pure (char 'Π' <> parens (pprNameLocal x <+> colon <+> pt) <> char '.' <> pe)

instance Pretty Chk where
  ppr (Inf s) = ppr s
  ppr (Lam xe) = do
    (x, e) <- unbind xe
    pe <- ppr e
    pure (char 'λ' <> pprNameLocal x <> (char '.' <+> pe))

instance Pretty Value where
  ppr (VLam xv) = do
    (x, v) <- unbind xv
    pv <- ppr v
    pure (char 'λ' <> pprNameLocal x <> char '.' <> pv)
  ppr VStar = pure (char '*')
  ppr (VPi xt_t)  = do
    (xt, e) <- unbind xt_t
    pe <- ppr e
    let ((x, Embed t), ()) = unrebind xt
    pt <- ppr t
    pure (char 'Π' <> parens (pprNameLocal x <+> colon <+> pt) <> char '.' <> pe)
  ppr (VVar x) = pure (pprNameLocal x)
  ppr (VApp f v) = (<+>) <$> ppr f <*> (parens <$> ppr v)

pprNameLocal :: Name a -> Doc
pprNameLocal = text . name2String
