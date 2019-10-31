{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances #-}
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
eval = runFreshMT . evalSyn mempty

evalPretty :: Context -> Syn -> Result Doc
evalPretty ctx = runFreshMT . (ppr <=< evalSyn ctx)

evalChkPretty :: Context -> Chk -> Result Doc
evalChkPretty ctx = runFreshMT . (ppr <=< evalChk ctx)

-- | Evaluation of terms
--
-- We must write an evaluator as types can now depend on values, and in order to
-- "compute the type" of a type, we must sometimes evaluate the "type expression"
--
evalSyn :: HasCallStack => Context -> Syn -> TypecheckM Value
evalSyn ctx syn = traceM ("evalSyn: " ++ show syn) >> case syn of
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
    (xp, p') <- unbind binding
    let ((x, Embed p),()) = unrebind xp
        vx = coerce x
    t <- evalChk ctx p
    t' <- evalChk ctx p'
    let xt = rebind (vx, Embed t) ()
    pure $ VPi (bind xt t')

  -- [WIP] Evaluation of Natural Numbers
  Nat -> pure VNat
  Zero -> pure VZero
  Succ k -> pure . VSucc =<< evalChk ctx k

  -- TODO eval bug here prollably (See notebook):
  NatElim m mz ms k -> do
    traceM $ "evalSyn: NatElim: " ++ show syn
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
      -- TODO "Neutral" term for VNatElim?
      VVar x -> do
        vm <- evalChk ctx m
        vmz <- evalChk ctx mz
        vms <- evalChk ctx ms
        pure (VNatElim vm vmz vms (VVar x))
      _ -> throwErrorTypecheckM "evalSyn: NatElim"

-- | Helper function for value application
vapp :: HasCallStack => Context -> Value -> Value -> TypecheckM Value
vapp ctx ve ve' = do
  pve <- render <$> ppr ve
  pve' <- render <$> ppr ve'
  traceM ("vapp: " ++ pve ++ " " ++ pve')
  case ve of
    VLam binder -> do
      (x, body) <- unbind binder
      pure (subst x ve' body)
    -- This case embodies a "free" function name in the context
    VVar x -> do
      case lookup x ctx of
        -- Free variable
        Nothing -> pure $ VApp (VVar x) ve'
        Just (VarInfo mv _) ->
          case mv of
            Nothing -> pure $ VApp (VVar x) ve'
            Just v -> vapp ctx v ve'
    -- This is a hack, we should have better methods of normalization:
    VNatElim vm vmz vms vk -> do
      case vk of
        VZero -> vapp ctx vmz ve'
        VSucc vl -> do
          vmsl <- vapp ctx vms vl
          vmsl' <- vapp ctx vmsl (VNatElim vm vmz vms vl)
          vapp ctx vmsl' ve'
        _ -> throwErrorTypecheckM $ "invalid apply: VNatElim: " ++ show ve
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
typeSyn ctx syn = traceM ("typeSyn: " ++ show syn) >> case syn of
  Var x -> case lookup (coerce x) ctx of
    Nothing -> throwErrorTypecheckM ("typeSyn: unknown identifier: " ++ show x)
    Just (VarInfo v t) -> pure t
  Ann e p -> do
    typeChk ctx p VStar
    t <- evalChk ctx p
    typeChk ctx e t
    pure t
  App e e' -> do

    pe <- render <$> ppr e
    pe' <- render <$> ppr e'
    traceM $ "typeSyn: " ++ pe ++ " applied to " ++ pe'

    sigma <- do
      sigma' <- typeSyn ctx e
      case sigma' of
        VApp ve ve' -> vapp ctx ve ve'
        _ -> pure sigma'
    case sigma of
      VPi binding -> do
        psigma <- render <$> ppr sigma
        traceM $ "typeSyn: Sigma: " ++ psigma
        (xt, t') <- unbind binding
        let ((x, Embed t), ()) = unrebind xt
        px <- ppShow x
        pt <- ppShow t
        traceM $ "typeSyn: 'unrebind xt': " ++ px ++ " has type " ++ pt
        typeChk ctx e' t
        ve' <- evalChk ctx e'
        pure (subst (coerce x) ve' t')
      _ -> throwErrorTypecheckM ("illegal application: " ++ show sigma)
  Star    -> pure VStar
  Pi xp_p' -> do
    (xp, p') <- unbind xp_p'
    let ((x,Embed p), ()) = unrebind xp
    typeChk ctx p VStar
    t <- evalChk ctx p
    let varInfo = VarInfo Nothing t
    typeChk (insert (coerce x) varInfo ctx) p' VStar
    pure VStar
  -- [WIP] Type "synthesis" of Natural number terms
  Nat -> pure VStar
  Zero -> pure VNat
  Succ k -> do
    typeChk ctx k VNat
    pure VNat
  NatElim m mz ms k -> do
    typeChk ctx m (tarr VNat VStar)
    vm <- evalChk ctx m
    traceM $ "Typechecking: " ++ (show mz)
    traceM $ "as the type: " ++ (show vm)
    traceM $ "but was before: " ++ (show m)
    typeChk ctx mz =<< vapp ctx vm VZero
    vk <- evalChk ctx k
    vmk <- vapp ctx vm vk
    typeChk ctx ms =<<
      pure . VPi . bind (mkVUniTele "l" VNat) . tarr vmk =<<
        vapp ctx vm (VSucc (VVar (s2n "l")))
    typeChk ctx k VNat
    pure vmk

tarr :: Type -> Type -> Type
tarr a b = VPi (bind (mkVUniTele "_" a) b)

-- | Check the type of a given type-checkable term
typeChk :: HasCallStack => Context -> Chk -> Type -> TypecheckM ()
typeChk ctx chk v = traceM ("typeChk: " ++ show chk) >> case chk of
  Inf e -> do
    v' <- typeSyn ctx e
    unless (aeq v v') $
      throwErrorTypecheckM $ unlines
        [ "type mismatch syn:"
        , "  expected: "++ show v
        , "  but got: " ++ show v'
        , "  ENV: "
        , show ctx
        ]

  Lam x_e -> case v of
    VPi xt_t'-> do
      (x , e) <- unbind x_e
      (xt, t') <- unbind xt_t'
      let ((_,Embed t),_) = unrebind xt
          varInfo = VarInfo Nothing t
      typeChk (insert (coerce x) varInfo ctx) e t'
    -- A substitution for 've' may have occurred such that it's not in it's
    -- normal form yet, and before type checking this lambda, we must force its
    -- typexv <- .
    VApp ve ve' -> typeChk ctx chk =<< vapp ctx ve ve'
    _ -> throwErrorTypecheckM $ unlines
        [ "type mismatch lam: "
        , "  expected VPi, but got: "++ show v
        , "  ENV: "
        , show ctx
        ]

----------------------------------------
-- Normalize
----------------------------------------

-- Anytime a variable that has a value is looked up, we need to normalize its
-- substitution; or, every time a substitution is made, we need to normalize.

----------------------------------------
-- DSL for term easier construction
----------------------------------------

chk = Inf
svar = Var . s2n
var = chk . svar
vvar = VVar . s2n

lam x = Lam . bind (s2n x)
vlam x = VLam . bind (s2n x)
pi' x t t' = chk $ Pi (bind (mkUniTele x t) t')
vpi x t t' = VPi (bind (mkVUniTele x t) t')

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

succ' :: Syn -> Chk
succ' = Inf . Succ . Inf

-- The reason this didn't work on its own:
--
--   N.B.
--     The "paper" code implements "natElim" in terms of a value that already
--     exists in the Context. If you define 'natElim' like this, it is not yet a
--     value, but since "Lam" is a "Chk" value, we cannot typecheck the Chk value,
--     without first giving it a type by annotating it. However, in order to
--     actually "apply" the lambda value 'natElim' to and values at all, we must
--     have a 'Syn' value as the function being applied. Thus, we need a _value_
--     'natElim' in the Context to construct a function "plus" that applies
--     "natElim" to arguments (as Var "natElim" is a 'Syn' value and not a 'Chk'
--     value).
natElim =
  lam "x" $
    lam "y" $
      lam "z" $
        lam "a" $
          Inf (NatElim (var "x") (var "y") (var "z") (var "a"))

natElim' =
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

vnatElim' =
  pi' "m" (arr (Inf Nat) (Inf Star)) $
    arr (Inf (App (svar "m") (Inf Zero))) $
      arr (pi' "l" (Inf Nat) (arr (Inf (App (svar "m") (var "l"))) (Inf (App (svar "m") (Inf (Succ (var "l"))))))) $
        pi' "k" (Inf Nat) (Inf (App (svar "m") (var "k")))

arr = pi' "_"
varr = vpi "_"

-- | Should we put the natElim value, or its type in this context? Why are
-- there two contexts? (see repLP lpve and lpte arguments in the
-- paper/LambdaPi.hs code).
--
--   There are two contexts because in one
stdlib :: Context
stdlib = fromList
  [ (s2n "natElim", VarInfo { varValue = Just natElim', varType = vnatElim }) ]

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

stdlib_plus_test =
  App (Var $ s2n "natElim") $
    lam "_" $ arr (Inf Nat) (Inf Nat)

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
    (xt, e) <- unbind xt_t
    pe <- ppr e
    let ((x, Embed t), ()) = unrebind xt
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
    (xt, e) <- unbind xt_t
    pe <- ppr e
    let ((x, Embed t), ()) = unrebind xt
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
