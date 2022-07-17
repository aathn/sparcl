{-# LANGUAGE RecursiveDo #-}

module Language.Sparcl.Eval where

import           Language.Sparcl.Core.Syntax
import           Language.Sparcl.Exception
import           Language.Sparcl.Value

import           Control.Monad.Except
import           Data.Maybe                  (fromMaybe)

-- import           Debug.Trace                 (trace)
import           Language.Sparcl.Pretty      hiding ((<$>))

evalFBind :: Env -> Bind Name -> Env
evalFBind env ds =
    let ev   = map (\(n,_,e) -> (n, evalF env' e)) ds
        env' = extendsEnv ev env
    in env'

mkValFun :: Value -> Value -> Value
mkValFun (VFun (env, n, e)) v = evalF (extendEnv n v env) e
mkValFun (VOp f) v = f v
mkValFun (VLift f _) v = f v
mkValFun vf _ =
  rtError $ text "expected a function, but found " <> ppr vf

mkValBool :: Value -> Bool
mkValBool v =
  case v of
    VCon c [] | c == conTrue -> True
    VCon c [] | c == conFalse -> False
    _ -> rtError $ text "expected bool but found " <> ppr v

evalF :: Env -> Exp Name -> Value
evalF env expr = case expr of
  Lit l -> VLit l
  Var n ->
    lookupEnvStrict n env

  App e1 e2 ->
    let v1 = evalF env e1
        v2 = evalF env e2
    in
      mkValFun v1 v2

  Abs n e ->
    VFun (env, n, e)

  Con q es ->
    VCon q $ map (evalF env) es

  Case e0 pes ->
    let v0 = evalF env e0
    in evalCase evalF env v0 pes

  RCase e0 pes ->
    let v0 = evalF env e0
    in evalCaseF env v0 pes

  Lift ef eb ->
    let v1 = evalF env ef
        v2 = evalF env eb
    in
      VLift (mkValFun v1) (mkValFun v2)

  Let ds e ->
    let env' = evalFBind env ds
    in evalF env' e

  FApp e1 e2 ->
    let v1 = evalF env e1
        v2 = evalF env e2
    in
      case v1 of
       VFun (env', n, e) -> evalF (extendEnv n v2 env') e
       VLift f _ -> f v2
       _ ->
         rtError $ text "expected a reversible function, but found " <> ppr v1

  BApp e1 e2 ->
    let v1 = evalF env e1
        v2 = evalF env e2
    in
      case v1 of
       VFun (env', n, e) ->
         let res = evalB env' v2 e
         in lookupEnvStrict n res
       VLift _ g -> g v2
       _ ->
         rtError $ text "expected a reversible function, but found " <> ppr v1

  RPin n e1 e2 ->
    let v1 = evalF env e1
        v2 = evalF (extendEnv n v1 env) e2
        c = nameTuple 2
    in
      VCon c [v1, v2]


evalB :: Env -> Value -> Exp Name -> Env
evalB env v expr = case expr of
  Var n ->
    case lookupEnv n env of
      Nothing -> singletonEnv n v
      Just _ -> emptyEnv

  Lit _ ->
    emptyEnv

  App _ _  ->
    emptyEnv

  Abs n e ->
    case v of
      VFun (_, n', _) | n == n' ->
                         emptyEnv
      _ ->
        rtError $ text "mismatching lambdas during backwards evaluation: " <>
                   ppr (Abs n e) <> text " =/= " <> ppr v

  Con q es ->
    case v of
      VCon q' vs | q == q' ->
                     foldl unionEnv emptyEnv $ zipWith (evalB env) vs es
      _ ->
        rtError $ text "mismatching constructors during backwards evaluation: " <>
                   ppr (Con q es) <> text " =/= " <> ppr v

  Case e0 pes ->
    let v0 = evalF env e0
    in evalCase (\env' e -> evalB env' v e) env v0 pes

  RCase e0 pes ->
    evalCaseB env v e0 pes

  Lift _ _ ->
    emptyEnv

  Let ds e ->
    let env' = evalFBind env ds
    in evalB env' v e

  FApp e1 e2 ->
    let v1 = evalF env e1
        v2 =
          case v1 of
            VFun (env', n, e) ->
              lookupEnvStrict n (evalB env' v e)
            VLift _ g ->
              g v
            _ ->
              rtError $ text "expected a reversible function, but found " <> ppr v1
    in
      evalB env v2 e2

  BApp e1 e2 ->
    let v1 = evalF env e1
        v2 =
          case v1 of
            VFun (env', n, e) ->
              evalF (extendEnv n v env') e
            VLift f _ ->
              f v
            _ ->
              rtError $ text "expected a reversible function, but found " <> ppr v1
    in
      evalB env v2 e2

  RPin n e1 e2 ->
    let c = nameTuple 2
        (v1,v2) =
          case v of
            VCon c' [x, y] | c == c' -> (x, y)
            _ ->
              rtError $ text "expected a tuple, but found " <> ppr v
        env1 = evalB env v1 e1
        env2 = evalB (extendEnv n v1 env) v2 e2
    in
      unionEnv env1 env2


evalCase :: (Env -> Exp Name -> a) -> Env -> Value -> [ (Pat Name, Exp Name) ] -> a
evalCase _    _   v [] = rtError $ text "pattern match error" <+> ppr v
evalCase eval env v ((p, e):pes) =
  case findMatch v p of
    Just binds -> eval (extendsEnv binds env) e
    _          -> evalCase eval env v pes

findMatch :: Value -> Pat Name -> Maybe [ (Name, Value) ]
findMatch v (PVar n) = return [(n, v)]
findMatch (VCon q vs) (PCon q' ps) | q == q' && length vs == length ps =
                                       concat <$> zipWithM findMatch vs ps
findMatch _ _ = Nothing


evalCaseF :: Env -> Value -> [ (Pat Name, Exp Name, Exp Name) ] -> Value
evalCaseF env v0 alts = go [] alts
  where
    go :: [Exp Name] -> [ (Pat Name, Exp Name, Exp Name) ] -> Value
    go _       [] = rtError $ text "pattern match failure (fwd): " <> ppr v0
    go checker ((p,e,ch) : pes) =
      case findMatch v0 p of
        Nothing ->
          go (ch:checker) pes
        Just binds ->
          let vres = evalF (extendsEnv binds env) e
              !()  = checkAssert ch checker vres
          in vres

    checkAssert :: Exp Name -> [Exp Name] -> Value -> ()
    checkAssert ch checker res =
      let v  = mkValBool (mkValFun (evalF env ch) res)
          vs = map (\c -> mkValBool (mkValFun (evalF env c) res)) checker
      in
        if (not v || or vs) then
          rtError $ text "Assertion failed (fwd)"
        else
          ()


evalCaseB :: Env -> Value -> Exp Name -> [ (Pat Name, Exp Name, Exp Name) ] -> Env
evalCaseB env vres e0 alts =
  let (v, env1) = go [] alts
      env2      = evalB env v e0
  in
    unionEnv env1 env2
  where
    mkAssert :: Pat Name -> Value -> Bool
    mkAssert p v = case findMatch v p of
                     Just _ -> True
                     _      -> False

    go _ [] = rtError $ text "pattern match failure (bwd)"
    go checker ((p,e,ch):pes) =
      if mkValBool (mkValFun (evalF env ch) vres) then
        let env1 = evalB env vres e
            xs = freeVarsP p
            v0 = fillPat p $ zip xs (map (\x -> lookupEnvStrict x env1) xs)
            !() = if any ($ v0) checker then () else
                    rtError $ text "Assertion failed (bwd)"
        in
          (v0, removesEnv xs env1)
      else
        go (mkAssert p:checker) pes

    fillPat :: Pat Name -> [ (Name, Value) ] -> Value
    fillPat (PVar n) bs =
      fromMaybe (error "Shouldn't happen") (lookup n bs)

    fillPat (PCon c ps) bs =
      VCon c (map (flip fillPat bs) ps)

