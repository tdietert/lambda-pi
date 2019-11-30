{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE LambdaCase                 #-}

module LambdaPi
where

import Control.Monad                    ((<=<), unless)
import Control.Monad.Except             (MonadError, throwError)
import Data.Coerce                      (coerce)
import Data.Map                         (Map, insert, lookup, fromList)
import Data.String                      (IsString)
import Data.Typeable                    (Typeable)
import Debug.Trace                      (traceM)
import GHC.Exts                         (toList)
import GHC.Generics                     (Generic)
import GHC.Stack                        (HasCallStack, callStack)
import Prelude                          hiding (lookup, pi)
import Text.PrettyPrint                 (Doc, (<+>), brackets, char, colon, parens, render, text)

import Unbound.Generics.LocallyNameless

----------------------------------------
--  Lambda-Pi Terms
----------------------------------------

-- | Variables for Type-synthesizable expressions
type Var = Name Syn

-- | The binding pattern for pi-terms
type PiBind expr = (Var, Embed expr)

type Rebindable expr = (Typeable expr, Alpha expr)

-- | Smart constructor for the PiBind type
mkPiBind :: Rebindable expr => [Char] -> expr -> PiBind expr
mkPiBind x e = (s2n x, Embed e)

-- | Type-inferable (synthesizable) terms
data Syn
  = Var Var -- ^ Free and bound variables
  | Ann Chk Chk -- ^ Annoted terms
  | App Syn Chk -- ^ Application
  | Pi (Bind (PiBind Chk) Chk)-- ^ The term for arrow types
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
  | Lam (Bind Var Chk) -- ^ Lambda term, must be "checked"
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

type VPiBind = (VVar, Embed Value)

mkVPiBind :: [Char] -> Value -> VPiBind
mkVPiBind x e = (s2n x, Embed e)

-- | "Evaluated" expressions (Syn + Chck) are values
--
--  Note:
--    Nested application values may need to be "normalized" after a substituion
--    occurs while evaluating the parent application expression or after the LHS
--    (lambda) expression is fully evaluated; For instance, the LHS of the
--    application value may be a variable that is bound by some outer lambda
--    abstraction, and could produce a value with redexes that needs to be
--    normalized:
--
--      λa.NatElim (λ_.Nat -> Nat) (λn.n) (λk.λrec.λn.S((rec) (n))) a
--
--    The NatElim value can be further reduced after substitution of the
--    variable 'a' for a value, returning either λn.n or λk.λrec.λn.S(rec n)
--    depending on the value of 'a'.
--
data Value
  = VLam (Bind VVar Value) -- ^ An evaluated lambda abstraction
  | VStar -- ^ The evaluated type of 'Star'
  | VPi (Bind VPiBind Value) -- ^ A type abstraction
  | VVar VVar -- ^ A free variable, "neutral" term
  | VApp Value Value -- ^ An evaluated application expression
  | VNat -- ^ The type for Natural Numbers
  | VZero -- ^ Peano Zero
  | VSucc Value -- ^ Peano Successor
  | VNatElim Value Value Value Value -- ^ The "Eliminator" for Natural Numbers
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
eval = unsafeEval mempty

unsafeEval :: Context -> Syn -> Result Value
unsafeEval ctx = runFreshMT . evalSyn ctx

evalSynPretty :: Context -> Syn -> Result Doc
evalSynPretty = evalPretty evalSyn

evalChkPretty :: Context -> Chk -> Result Doc
evalChkPretty = evalPretty evalChk

evalPretty
  :: (Context -> a -> TypecheckM Value)
  -> Context
  -> a
  -> Result Doc
evalPretty runTypecheckM ctx a = do
  runFreshMT $ do
    v <- runTypecheckM ctx a
    ppr =<< normalize ctx v

-- | Evaluation of terms
--
-- We must write an evaluator as types can now depend on values, and in order to
-- "compute the type" of a type, we must sometimes evaluate the "type expression"
--
evalSyn :: HasCallStack => Context -> Syn -> TypecheckM Value
evalSyn ctx syn = case syn of
  Var x ->
    let vx = coerce x in
    case lookup vx ctx of
      Nothing -> pure (VVar vx)
      Just (VarInfo mv t) ->
        case mv of
          Nothing -> pure (VVar vx)
          Just v -> pure v
  Ann e _ -> evalChk ctx e
  App e e' -> do
    ve <- evalSyn ctx e
    ve' <- evalChk ctx e'
    vapp ctx ve ve'
  Star -> pure VStar
  Pi binding -> do
    ((x, Embed p), p') <- unbind binding
    let vx = coerce x
    t <- evalChk ctx p
    t' <- evalChk ctx p'
    let xt = (vx, Embed t)
    pure $ VPi (bind xt t')
  Nat -> pure VNat
  Zero -> pure VZero
  Succ k -> pure . VSucc =<< evalChk ctx k
  NatElim m mz ms k -> do
    vk <- evalChk ctx k
    case vk of
      VZero -> evalChk ctx mz
      VSucc l -> do
        vm <- evalChk ctx m
        vmz <- evalChk ctx mz
        vms <- evalChk ctx ms
        let rec = VNatElim vm vmz vms l
        vmsl <- vapp ctx vms l
        res <- vapp ctx vmsl rec
        pure res
      -- In the case that 'k' is a free variable:
      VVar x -> do
        vm <- evalChk ctx m
        vmz <- evalChk ctx mz
        vms <- evalChk ctx ms
        pure (VNatElim vm vmz vms (VVar x))
      _ -> throwErrorTypecheckM "evalSyn: NatElim"

-- | Helper function for applying lambda abstraction values to argument values
-- that always normalizes its arguments and resulting value.
vapp :: HasCallStack => Context -> Value -> Value -> TypecheckM Value
vapp ctx ve ve' = do
  case ve of
    VLam binder -> do
      (x, body) <- unbind binder
      normalize ctx (subst x ve' body)
    -- This case is for the rare occasion when we are constructing "neutral"
    -- expressions for evaluation _during_ evaluation of another expressions, or
    -- when fully evaluating the LHS of an application expression whose LHS
    -- value is a bound variable that has not yet been substituted.
    VVar x -> do
      case lookup x ctx of
        -- Free variable
        Nothing -> pure $ VApp (VVar x) ve'
        Just (VarInfo mv _) ->
          case mv of
            Nothing -> pure $ VApp (VVar x) ve'
            Just v -> vapp ctx v ve'
    _ -> throwErrorTypecheckM $ "invalid apply: " ++ show ve


-- | Evaluate a checkable expression
evalChk :: HasCallStack => Context -> Chk -> TypecheckM Value
evalChk ctx chk = case chk of
  Inf syn -> evalSyn ctx syn
  Lam binding -> do
    (x, e) <- unbind binding
    ve <- evalChk ctx e
    pure $ VLam (bind (coerce x) ve)

-- We store types in their evaluated form
type Type = Value
type Context = Map VVar VarInfo

data VarInfo = VarInfo { varValue :: Maybe Value, varType :: Type }
  deriving Show

-- | Typecheck an expression whose type is synthesizable
typecheck :: HasCallStack => Syn -> Result Type
typecheck = runFreshMT . typeSyn mempty

typecheckPretty :: HasCallStack => Syn -> Result Doc
typecheckPretty = typecheckPretty' mempty

typecheckPretty' :: HasCallStack => Context -> Syn -> Result Doc
typecheckPretty' ctx = runFreshMT . (ppr <=< typeSyn ctx)

-- | Compute the type of a term whose type can be synthesized given a context
typeSyn :: HasCallStack => Context -> Syn -> TypecheckM Type
typeSyn ctx = \case
  Var x -> case lookup (coerce x) ctx of
    Nothing -> throwErrorTypecheckM ("typeSyn: unknown identifier: " ++ show x)
    Just (VarInfo v t) -> pure t
  Ann e p -> do
    typeChk ctx p VStar
    t <- evalChk ctx p
    typeChk ctx e t
    pure t
  App e e' -> do
    sigma <- typeSyn ctx e
    case sigma of
      VPi binding -> do
        ((x, Embed t), t') <- unbind binding
        typeChk ctx e' t
        ve' <- evalChk ctx e'
        normalize ctx (subst (coerce x) ve' t')
      _ -> throwErrorTypecheckM ("illegal application: " ++ show sigma)
  Star    -> pure VStar
  Pi xp_p' -> do
    ((x, Embed p), p') <- unbind xp_p'
    typeChk ctx p VStar
    t <- evalChk ctx p
    let varInfo = VarInfo Nothing t
    typeChk (insert (coerce x) varInfo ctx) p' VStar
    pure VStar
  Nat -> pure VStar
  Zero -> pure VNat
  Succ k -> do
    typeChk ctx k VNat
    pure VNat
  NatElim m mz ms k -> do
    typeChk ctx m (tarr VNat VStar)
    vm <- evalChk ctx m
    typeChk ctx mz =<< vapp ctx vm VZero
    vk <- evalChk ctx k
    vmk <- vapp ctx vm vk
    t' <-
      pure . VPi . bind (mkVPiBind "l" VNat) . tarr vmk =<<
        vapp ctx vm (VSucc (VVar (s2n "l")))
    typeChk ctx ms t'
    typeChk ctx k VNat
    pure vmk

-- | A function type whose return type doesn't depend on the argument value
tarr :: Type -> Type -> Type
tarr a b = VPi (bind (mkVPiBind "_" a) b)

-- | Check the type of a given type-checkable term
typeChk :: HasCallStack => Context -> Chk -> Type -> TypecheckM ()
typeChk ctx chk v = case chk of
  Inf e -> do
    v' <- typeSyn ctx e
    -- If not alpha equivalent, fail
    unless (aeq v v') $
      throwErrorTypecheckM $ unlines
        [ "type mismatch:"
        , "  expected: "++ show v
        , "  but got: " ++ show v'
        ]

  Lam x_e -> case v of
    VPi xt_t'-> do
      (x , e) <- unbind x_e
      ((_, Embed t), t') <- unbind xt_t'
      let varInfo = VarInfo Nothing t
      typeChk (insert (coerce x) varInfo ctx) e t'
    _ -> throwErrorTypecheckM $ unlines
        [ "type mismatch lam: "
        , "  expected VPi, but got: "++ show v
        ]

----------------------------------------
-- Normalize
----------------------------------------

-- | Normalize a value constructed by a substitution
--
-- The need for this function stems from the evalution strategy
-- implicitly chosen during this dependent type theory study: call by value.
--
-- Note:
--   When function application is evaluated, or when typechecking the App
--   expression, a variable substitution is performed to either compute the result
--   of the function application, or compute the return type of a value. In both
--   cases, a value is subsituted in place of a variable in the body of either a
--   lambda or a pi term; The resulting body needs to be normalized, as a VApp
--   value may contain a non-neutral term on the LHS that can be further
--   normalized. Un-normalized terms cause the evalutor to choke and throw errors,
--   as it always expects normalized terms. By calling 'normalize' on a resulting
--   expression after a substitution is performed should prevent these errors;
--   i.e. using `vapp` every time we wish to construct an application value.
--
normalize :: Context -> Value -> TypecheckM Value
normalize ctx v =
  case v of
    VVar x -> pure (VVar x)
    VLam binder -> do
      (x, body) <- unbind binder
      pure . VLam . bind x =<< normalize ctx body
    VStar -> pure VStar
    VPi binder -> do
      ((x, Embed t), t') <- unbind binder
      nt <- normalize ctx t
      let nxt = mkVPiBind (name2String x) nt
      nt' <- normalize ctx t'
      pure $ VPi (bind nxt nt')
    VApp ve ve' -> do
      nve <- normalize ctx ve
      nve' <- normalize ctx ve'
      vapp ctx nve nve'
    VNat -> pure VNat
    VZero -> pure VZero
    VSucc v -> pure . VSucc =<< normalize ctx v
    VNatElim m mz ms k -> do
      nk <- normalize ctx k
      case nk of
        VZero -> normalize ctx mz
        VSucc l -> do
          nm <- normalize ctx m
          nmz <- normalize ctx mz
          nms <- normalize ctx ms
          nl <- normalize ctx l
          let rec = VNatElim nm nmz nms nl
          nmsl <- vapp ctx nms l
          vapp ctx nmsl rec
        VVar x -> pure $ VNatElim m mz ms nk
        _ -> throwErrorTypecheckM "normalize: VNatElim"

----------------------------------------
-- DSL for term easier construction
----------------------------------------

chk = Inf
svar = Var . s2n
var = chk . svar
vvar = VVar . s2n

lam x = Lam . bind (s2n x)
vlam x = VLam . bind (s2n x)
pi' x t t' = chk $ Pi (bind (mkPiBind x t) t')
vpi x t t' = VPi (bind (mkVPiBind x t) t')

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

zero :: Chk
zero = Inf Zero

succ' :: Syn -> Syn
succ' = Succ . Inf

natElim =
  vlam "x" $
    vlam "y" $
      vlam "z" $
        vlam "a" $
          VNatElim (vvar "x") (vvar "y") (vvar "z") (vvar "a")

-- | The type of natElim
vnatElim :: Value
vnatElim =
  vpi "m" (varr VNat VStar) $
    varr (VApp (vvar "m") (VZero)) $
      varr (vpi "l" VNat (varr (VApp (vvar "m") (vvar "l")) (VApp (vvar "m") (VSucc (vvar "l"))))) $
        vpi "k" VNat (VApp (vvar "m") (vvar "k"))

arr = pi' "_"
varr = vpi "_"

----------------------------------------
-- Example
----------------------------------------

stdlib :: Context
stdlib = fromList
  [ (s2n "natElim", VarInfo { varValue = Just natElim, varType = vnatElim }) ]

stdlib_plus :: Syn
stdlib_plus =
  App
    (App
      (App
         (Var (s2n "natElim"))
         (lam "_" $ arr (Inf Nat) (Inf Nat))
      )
      (lam "n" (var "n"))
    )
    (lam "k" $ lam "rec" $ lam "n" $ Inf (Succ (Inf (App (svar "rec") (var "n")))))

-- | Evaluates 1 + 2
--
-- λ> plusExample
-- Right (VSucc (VSucc (VSucc VZero)))
--
plusExample :: Result Value
plusExample =
    unsafeEval stdlib $
      App (App stdlib_plus one) two
  where
    one = Inf (succ' Zero)
    two = Inf (Succ one)

----------------------------------------
-- Pretty Printer
----------------------------------------

ppShow :: (Fresh m, Pretty a) => a -> m String
ppShow = fmap render . ppr

class Pretty a where
  ppr :: (Applicative m, Fresh m) => a -> m Doc

instance Pretty Syn where
  ppr (Var x) = pure (pprNameLocal x)
  ppr (App e e') = do
    pe <- ppr e
    pe' <- ppr e'
    pure $ parens pe <+> parens pe'
  ppr (Ann e t) = do
    pe <- ppr e
    pt <- ppr t
    pure (parens pe <+> colon <+> pt)
  ppr Star = pure (char '*')
  ppr (Pi xt_t) = do
    ((x, Embed t), e) <- unbind xt_t
    pe <- ppr e
    pt <- ppr t
    let ppx = pprNameLocal x
    if ppx == (text "_")
      then pure $
        pt <+> text "->" <+> pe
      else pure $
        char 'Π' <> parens (ppx <+> colon <+> pt) <> char '.' <> pe

  ppr Nat = pure $ text "Nat"
  ppr Zero = pure $ char 'Z'
  ppr (Succ k) = pure . (text "S" <>) . parens =<< ppr k
  ppr (NatElim m mz ms k) = do
    pm <- ppr m
    pmz <- ppr mz
    pms <- ppr ms
    pk <- ppr k
    pure $ text "NatElim" <+> pm <+> pmz <+> pms <+> pk

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
    ((x, Embed t), e) <- unbind xt_t
    pe <- ppr e
    pt <- ppr t
    let ppx = pprNameLocal x
    if ppx == (text "_")
      then pure $
        pt <+> text "->" <+> pe
      else pure $
        char 'Π' <> parens (ppx <+> colon <+> pt) <> char '.' <> pe
  ppr (VVar x) = pure (pprNameLocal x)
  ppr (VApp f v) = do
    pf <- ppr f
    pv <- ppr v
    pure $ parens pf <+> parens pv

  ppr VNat = pure (text "Nat")
  ppr VZero = pure (char 'Z')
  ppr (VSucc k) = pure . (text "S" <>) . parens =<< ppr k
  ppr (VNatElim m mz ms k) = do
    pm <- pprParens m
    pmz <- pprParens mz
    pms <- pprParens ms
    pk <- pprParens k
    pure $ text "NatElim" <+> pm <+> pmz <+> pms <+> pk

instance Pretty (Name Value) where
  ppr x = pure (pprNameLocal x)

pprParens :: (Applicative m, Fresh m, Pretty a) => a -> m Doc
pprParens = fmap parens . ppr

pprNameLocal :: Name a -> Doc
pprNameLocal = text . name2String
