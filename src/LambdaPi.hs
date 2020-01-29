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
import Data.Foldable                    (foldlM)
import Control.Monad.Except             (MonadError, throwError)
import Data.Coerce                      (coerce)
import Data.Map                         (Map, fromList)
import qualified Data.Map               as Map
import Data.String                      (IsString)
import Data.Typeable                    (Typeable)
import Debug.Trace                      (trace, traceM)
import GHC.Exts                         (toList)
import GHC.Generics                     (Generic)
import GHC.Stack                        (HasCallStack, callStack)
import Prelude                          hiding (lookup, pi)
import Text.PrettyPrint                 (Doc, (<+>), brackets, char, colon, parens, render, text)

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Name (Name(..))

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
  -- Length-indexed Vectors
  | Vec Chk Chk
  | Nil Chk
  | Cons Chk Chk Chk Chk
  | VecElim Chk Chk Chk Chk Chk Chk
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
  | VNil Value -- ^ The empty Vector
  | VCons Value Value Value Value -- ^ The non-empty Vector
  | VVec Value Value -- ^ The type of Vectors
  | VVecElim Value Value Value Value Value Value -- ^ The "Eliminator" for Vectors
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
    case lookupVar x ctx of
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
    let varInfo = VarInfo Nothing t
    t' <- evalChk (insertVar x varInfo ctx) p'
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
  VecElim a m mn mc k xs -> do
    vmn <- evalChk ctx mn
    vmc <- evalChk ctx mc
    vxs <- evalChk ctx xs
    case vxs of
      VNil _ -> pure vmn
      VCons _ vl' vx' vxs' -> do
        va <- evalChk ctx a
        vm <- evalChk ctx m
        vk <- evalChk ctx k
        let rec = VVecElim va vm vmn vmc vl' vxs'
        vapps ctx vmc [vl', vx', vxs', rec]
      VVar x -> do
        va <- evalChk ctx a
        vm <- evalChk ctx m
        vk <- evalChk ctx k
        pure (VVecElim va vm vmn vmc vk (VVar x))
      _ -> throwErrorTypecheckM ("evalSyn: VecElim: " ++ show vxs)
  Nil a -> pure . VNil =<< evalChk ctx a
  Cons a k x xs ->
    VCons <$> evalChk ctx a
          <*> evalChk ctx k
          <*> evalChk ctx x
          <*> evalChk ctx xs
  Vec a k ->
    VVec <$> evalChk ctx a
         <*> evalChk ctx k

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
      case lookupVar x ctx of
        -- Free variable
        Nothing -> pure $ VApp ve ve'
        Just (VarInfo mv _) ->
          case mv of
            Nothing -> pure $ VApp ve ve'
            Just v -> vapp ctx v ve'
    VNatElim m mz ms k ->
      case k of
        VVar _ -> pure $ VApp ve ve'
        _ -> error "wut"
    VApp f _ -> do
      case f of
        VVar x -> pure $ VApp ve ve'
        _ -> do
          napp <- normalize ctx ve
          vapp ctx napp ve'
    _ -> throwErrorTypecheckM $ unlines
           ["invalid apply:"
           , show ve
           , "  to"
           , show ve'
           ]

vapps :: HasCallStack => Context -> Value -> [Value] -> TypecheckM Value
vapps ctx = foldlM (vapp ctx)

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

-- | A Context maps a variable to the variables type and value
--
-- TODO Make a "Pretty" instance for debugging
type Context = Map VVar VarInfo

insertVar :: Name a -> VarInfo -> Context -> Context
insertVar nm vinfo ctx =
  trace ("Inserting " ++ show nm ++ " as " ++ show vinfo) $
    Map.insert (coerce nm) vinfo ctx

lookupVar :: Name a -> Context -> Maybe VarInfo
lookupVar nm ctx =
  trace ("Looking up " ++ show nm) $
    Map.lookup (coerce nm) ctx

data VarInfo = VarInfo { varValue :: Maybe Value, varType :: Type }
  deriving Show

-- | Typecheck an expression whose type is synthesizable
typecheck :: HasCallStack => Syn -> Result Type
typecheck = runFreshMT . typeSyn mempty

typecheckPretty :: HasCallStack => Syn -> Result Doc
typecheckPretty syn =
  trace ("typecheckPretty: " ++ show syn) $
    typecheckPretty' mempty syn

typecheckPretty' :: HasCallStack => Context -> Syn -> Result Doc
typecheckPretty' ctx = runFreshMT . (ppr <=< typeSyn ctx)

-- | Compute the type of a term whose type can be synthesized given a context
typeSyn :: HasCallStack => Context -> Syn -> TypecheckM Type
typeSyn ctx syn = case syn of
  Var x -> case lookupVar x ctx of
    Nothing -> throwErrorTypecheckM $
      "typeSyn: unknown identifier: " ++ show x ++ " given " ++ show ctx
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
    typeChk (insertVar x varInfo ctx) p' VStar
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
  Vec a k -> do
    typeChk ctx a VStar
    typeChk ctx k VNat
    pure VStar
  Nil a -> do
    typeChk ctx a VStar
    va <- evalChk ctx a
    pure (VVec va VZero)
  Cons a k x xs -> do
    typeChk ctx a VStar
    va <- evalChk ctx a
    typeChk ctx k VNat
    vk <- evalChk ctx k
    typeChk ctx x va
    typeChk ctx xs (VVec va vk)
    pure (VVec va (VSucc vk))
  VecElim a m mn mc k vs -> do
    typeChk ctx a VStar
    va <- evalChk ctx a
    -- typecheck m
    mTyp <-
      pure . VPi . bind (mkVPiBind "k" VNat) $
        tarr (VVec va (VVar (s2n "k"))) VStar
    typeChk ctx m mTyp
    vm <- evalChk ctx m
    -- typecheck mn
    mnTyp <- vapps ctx vm [VZero, VNil va]
    typeChk ctx mn mnTyp
    vmn <- evalChk ctx mn
    -- typecheck mc
    let vl@(VVar (Fn lstr _)) = VVar (s2n "l")
        vx@(VVar (Fn xstr _)) = VVar (s2n "x")
        vxs@(VVar (Fn xsstr _)) = VVar (s2n "xs")
    mcTyp <-
      pure .
        VPi . bind (mkVPiBind lstr VNat) .
          VPi . bind (mkVPiBind xstr va) .
            VPi . bind (mkVPiBind xsstr (VVec va vl)) =<< do
              lhs <- vapps ctx vm [vl, vxs]
              rhs <- vapps ctx vm [VSucc vl, VCons va vl vx vxs]
              pure $ tarr lhs rhs
    typeChk ctx mc mcTyp
    vmc <- evalChk ctx mc
    -- typecheck k
    typeChk ctx k VNat
    vk <- evalChk ctx k
    -- typehcheck vs
    typeChk ctx vs (VVec va vk)
    vvs <- evalChk ctx vs
    -- return type of VecElim
    vapps ctx vm [vk, vvs]


-- | A function type whose return type doesn't depend on the argument value
tarr :: HasCallStack => Type -> Type -> Type
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
      (x, e) <- unbind x_e
      ((_, Embed t), t') <- unbind xt_t'
      let varInfo = VarInfo Nothing t
      typeChk (insertVar x varInfo ctx) e t'
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
-- TODO Decide how this interacts with 'evalSyn'... since we represent
-- "unevaluated" terms as 'Syn' or 'Chk' expressions, but 'Value's can still be
-- "unevaluated", we end up having to duplicate a lot of the evaluation logic
-- for already-evaluated values (that may still contain redexes after
-- substitution. *A potential solution* is to parameterize the 'Syn' and 'Chk'
-- types with a type variable denoting if the expression could contain redexes
-- or not (is it "evaluatable" or "fully evaluated"?); These types could imply
-- when to recursively call 'eval', and prevent calling 'eval' on expressions
-- that are fully evaluated (e.g. the 'App' expression can produce expressions
-- that still need to be evaluated, preventing them from being prematurely
-- returned from the 'eval' functions if we added such a type index).
-- Furthermore, this would reduce the need for duplicating the AST between
-- 'Syn', 'Chk', and 'Value'.
--
--   [digression: perhaps adding GADTs could even further constrain the AST
--   preventing several invalid expression formations by types alone, but it may
--   be too complex with such "eliminator" values and types/values with many
--   term parameters ('VecElim', 'Cons', 'NatElim', etc.)]
--
normalize :: HasCallStack => Context -> Value -> TypecheckM Value
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
        _ -> throwErrorTypecheckM ("normalize: VNatElim: " ++ show nk)
    VNil a -> pure . VNil =<< normalize ctx a
    VCons a l x xs -> do
      na <- normalize ctx a
      nl <- normalize ctx l
      nx <- normalize ctx x
      nxs <- normalize ctx xs
      pure $ VCons na nl nx nxs
    -- TODO Cases for Vectors:
    VVec a n -> do
      na <- normalize ctx a
      nn <- normalize ctx n
      pure $ VVec na nn
    VVecElim a m mn mc k xs -> do
      -- here, we want to see if xs can be evaluated further:
      vmn <- normalize ctx mn
      vmc <- normalize ctx mc
      vxs <- normalize ctx xs
      case vxs of
        VNil _ -> pure vmn
        VCons _ vl' vx' vxs' -> do
          va <- normalize ctx a
          vm <- normalize ctx m
          vk <- normalize ctx k
          let rec = VVecElim va vm vmn vmc vl' vxs'
          vapps ctx vmc [vl', vx', vxs', rec]
        VVar x -> do
          va <- normalize ctx a
          vm <- normalize ctx m
          vk <- normalize ctx k
          pure (VVecElim va vm vmn vmc vk (VVar x))
        _ -> throwErrorTypecheckM ("normalize: VecElim: " ++ show vxs)

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

-- | Apply an expression to one or more expressions
apps :: Syn -> Chk -> [Chk] -> Syn
apps f x xs = foldl (\g arg -> App g arg) f (x:xs)

-- | Annotate a "checkable" term
ann :: Chk -> Chk -> Syn
ann e t = Ann e t

(<|) :: Syn -> Chk -> Syn
(<|) f x = App f x

zero, one, two :: Chk
zero = Inf Zero
one = Inf (succ' Zero)
two = Inf (Succ one)

succ' :: Syn -> Syn
succ' = Succ . Inf

natElim :: Value
natElim =
  vlam "x" $ vlam "y" $ vlam "z" $ vlam "a" $
    VNatElim (vvar "x") (vvar "y") (vvar "z") (vvar "a")

-- | The type of natElim
natElimTyp :: Type
natElimTyp =
  vpi "m" (varr VNat VStar) $
    varr (VApp (vvar "m") (VZero)) $
      varr (vpi "l" VNat (varr (VApp (vvar "m") (vvar "l")) (VApp (vvar "m") (VSucc (vvar "l"))))) $
        vpi "k" VNat (VApp (vvar "m") (vvar "k"))

vecElim :: Value
vecElim =
  vlam "a" $ vlam "m" $ vlam "mNil" $ vlam "mCons" $ vlam "k" $ vlam "vs" $
    VVecElim (vvar "a") (vvar "m") (vvar "mNil") (vvar "mCons") (vvar "k") (vvar "vs")

-- | The type of vecElim
vecElimTyp :: Type
vecElimTyp =
  vpi "a" VStar $
    vpi "m" (vpi "k" VNat (varr (VVec (vvar "a") (vvar "k")) VStar)) $
      varr
       (app2 (vvar "m") VZero (VNil (vvar "a")))
       (varr
         (vpi "l" VNat $
           vpi "x" (vvar "a") $
             vpi "xs" (VVec (vvar "a") (vvar "l")) $
               varr
                 (app2 (vvar "m") (vvar "l") (vvar "xs"))
                 (app2 (vvar "m") (VSucc (vvar "l"))
                   (VCons (vvar "a") (vvar "l") (vvar "x") (vvar "xs"))
                 )
         )
         (vpi "k" VNat $
           vpi "xs" (VVec (vvar "a") (vvar "k")) $
             app2 (vvar "m") (vvar "k") (vvar "xs")
         )
       )


app2 :: Type -> Type -> Type -> Type
app2 a b c = VApp (VApp a b) c

arr = pi' "_"
varr = vpi "_"

----------------------------------------
-- Example
----------------------------------------

stdlib :: Context
stdlib = fromList
  [ (s2n "natElim", VarInfo { varValue = Just natElim, varType = natElimTyp })
  , (s2n "vecElim", VarInfo { varValue = Just vecElim, varType = vecElimTyp })
  ]

stdlib_plus :: Syn
stdlib_plus =
  apps
    (Var (s2n "natElim"))
    (lam "_" $ arr (Inf Nat) (Inf Nat))
    [ lam "n" (var "n")
    , lam "k" $
        lam "rec" $
          lam "n" $
            Inf (Succ (Inf (App (svar "rec") (var "n"))))
    ]

stdlib_plus_typ :: Chk
stdlib_plus_typ =
  pi' "x" (chk Nat) .
    pi' "y" (chk Nat) $
      chk Nat

stdlib_append :: Syn
stdlib_append = Ann stdlib_append' stdlib_append_typ

stdlib_append' :: Chk
stdlib_append' =
  lam "a" . chk $
    apps
      (svar "vecElim")
      (var "a")
      [ lam "m" $ lam "_" $
          arr
            (pi' "n" (Inf Nat) (Inf (Vec (var "a") (var "n"))))
            (Inf (Vec (var "a") (chk $ apps stdlib_plus (var "m") [var "n"])))
      , lam "_" $ lam "v" $ var "v"
      , lam "m" $ lam "v" $ lam "vs" $ lam "rec" $ lam "n" $ lam "w" $
          chk $ Cons
            (var "a")
            (chk $ apps stdlib_plus (var "m") [var "n"])
            (var "v")
            (chk $ apps (svar "rec") (var "n") [var "w"])
      ]

stdlib_append_typ :: Chk
stdlib_append_typ =
  pi' "a" (chk Star) .
    pi' "m" (chk Nat) .
      pi' "v" (chk $ Vec (var "a") (var "m")) .
        pi' "n" (chk Nat) .
          pi' "w" (chk $ Vec (var "a") (var "n")) . chk $
            Vec (var "a") (chk $ apps stdlib_plus (var "m") [var "n"])

----------------------------------------
-- Examples
----------------------------------------

-- | Evaluates 1 + 2
--
-- λ> plusExample
-- Right (VSucc (VSucc (VSucc VZero)))
--
plusExample :: Result Value
plusExample =
    unsafeEval stdlib $
      App (App stdlib_plus one) two

-- | Evaluates 'append [1] [0,1]'
--
-- λ> appendExample
-- Right (VCons VNat (VSucc (VSucc (VSucc VZero))) VZero (VCons VNat (VSucc VZero) VZero (VCons VNat VZero (VSucc VZero) (VNil VNat))))
--
appendExample :: Result Value
appendExample =
    unsafeEval stdlib $
      apps stdlib_append vecType [one, l, two, r]
  where
    vecType = Inf Nat

    -- Length-indexed vector with a single element: [1]
    l =
      Inf $
        Cons vecType one zero $ Inf $
            Nil vecType

    -- Length-indexed vector with two elements: [0,1]
    r =
      Inf $
        Cons vecType one zero $ Inf $
          Cons vecType zero one $ Inf $
            Nil vecType

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
  -- TODO
  ppr _ = pure $ text "Not implemented yet"

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
  -- TODO
  ppr _ = pure $ text "Not implemented yet"

instance Pretty (Name Value) where
  ppr x = pure (pprNameLocal x)

pprParens :: (Applicative m, Fresh m, Pretty a) => a -> m Doc
pprParens = fmap parens . ppr

pprNameLocal :: Name a -> Doc
pprNameLocal = text . name2String
