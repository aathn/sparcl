{-# LANGUAGE ConstraintKinds #-}
module Language.Sparcl.Desugar (
  desugarExp, desugarTopDecls,
  runDesugar
  ) where

import           Data.Function                  (on)
import           Data.List                      (groupBy)
import           Data.Maybe                     (isJust)
import           Data.Void

import           Control.Monad.Reader

import           Language.Sparcl.SrcLoc
import qualified Language.Sparcl.Surface.Syntax as S

import           Language.Sparcl.Name

import qualified Language.Sparcl.Core.Syntax    as C
import           Language.Sparcl.Pass
import           Language.Sparcl.Typing.TCMonad

-- import Debug.Trace

type NameSource = Int -- de Brujin levels

-- Desugaring may refer to types, so it will use type checking monad.
type Desugar m a = MonadTypeCheck m => ReaderT NameSource m a

type MonadDesugar m = (MonadReader Int m, MonadTypeCheck m)

withNewName :: MonadDesugar m => (Name -> m r) -> m r
withNewName k = do
  i <- ask
  local (+1) (k (Generated i Desugaring))

withNewNames :: MonadDesugar m => Int -> ([Name] -> m r) -> m r
withNewNames n k = do
  i <- ask
  local (+ n) (k $ map (flip Generated Desugaring) [i..i+n-1])

runDesugar :: MonadTypeCheck m => Desugar m a -> m a
runDesugar m = runReaderT m 0

desugarExp :: forall m. MonadDesugar m => S.LExp 'TypeCheck -> m (C.Exp Name)
desugarExp (Loc _ expr) = go expr
  where
    go :: S.Exp 'TypeCheck -> m (C.Exp Name)

    go (S.Var (x, _)) = return $ C.Var x
    go (S.Lit l)      = return $ C.Lit l
    go (S.App e1 e2)  =
      C.App <$> desugarExp e1 <*> desugarExp e2

    go (S.Abs ps e) = desugarRHS [(ps, S.Clause e (S.HDecls () []) Nothing)]

    go (S.Con (c,_ty) es) =
      C.Con c <$> mapM desugarExp es

    go (S.Case e alts) = do
      e'  <- desugarExp e
      let (ps, cs) = unzip alts
      ps' <- mapM desugarPat ps
      if any (isJust . S.withExp) cs || any S.isLinPat ps then do
        alts' <- zipWith (\p (e1,e2) -> (p,e1,e2)) ps' <$> mapM convertClauseR cs
        return $ C.RCase e' alts'
        else do
        alts' <- zip ps' <$> mapM convertClauseU cs
        return $ C.Case e' alts'

    go S.Lift =
      withNewNames 2 $ \[x, y] ->
      return $ foldr C.Abs (C.Lift (C.Var x) (C.Var y)) [x,y]

    go (S.Sig e _) = desugarExp e

    go (S.Let (S.Decls v _) _) = absurd v
    go (S.Let (S.HDecls xinfo bss) e) =
      case bss of
        [] -> desugarExp e
        bs:rest -> do
          e' <- go (S.Let (S.HDecls xinfo rest) e)
          bs' <- mapM (\(Loc _ (S.DDef (n,ty) pcs)) -> do
                          r <- desugarRHS pcs
                          return (n, ty, r)) bs
          return $ C.Let bs' e'

    go (S.Let1 p1 e1 e2) =
      go $ S.Case e1 [(p1, S.Clause e2 (S.HDecls () []) Nothing)]

    go (S.Parens e) = desugarExp e

    go (S.Op (op, _ty) e1 e2) = do
      e1' <- desugarExp e1
      e2' <- desugarExp e2
      return $ C.App (C.App (C.Var op) e1') e2'

    go (S.FApp e1 e2)  =
      C.FApp <$> desugarExp e1 <*> desugarExp e2

    go (S.BApp e1 e2)  =
      C.BApp <$> desugarExp e1 <*> desugarExp e2

    go (S.RPin p1 e1 e2) = withNewName $ \n -> do
      p1' <- desugarPat p1
      e1' <- desugarExp e1
      e2' <- desugarExp e2
      return $ C.RPin n e1' $ C.Case (C.Var n) [(p1',e2')]

makeTupleExpC :: [C.Exp Name] -> C.Exp Name
makeTupleExpC [e] = e
makeTupleExpC es  = C.Con (nameTuple (length es)) es

makeTuplePatC :: [C.Pat Name] -> C.Pat Name
makeTuplePatC [p] = p
makeTuplePatC ps  = C.PCon (nameTuple (length ps)) ps

desugarRHS :: MonadDesugar m => [([S.LPat 'TypeCheck], S.Clause 'TypeCheck)] -> m (C.Exp Name)
desugarRHS pcs =
  let (pps, cs) = unzip pcs
      len = length $ head pps
      hasRev = len > 0 && (any (isJust . S.withExp) cs || any (S.isLinPat . last) pps)
  in withNewNames len $ \ns -> do
    body <-
      if not hasRev then do
        cs' <- mapM convertClauseU cs
        if len == 0 then
          return $ head cs'
          else do
          (e, psU) <- makePatternsU ns pps
          return $ C.Case e (zip psU cs')
      else do
        let nsU = init ns
            nR = last ns
            (ppsU, psR) = unzip $ map ((,) <$> init <*> last) pps
        cs' <- mapM convertClauseR cs
        psR' <- mapM desugarPat psR
        if len == 1 then
          return $ C.RCase (C.Var nR) (zipWith (\pR (e1,e2) -> (pR,e1,e2)) psR' cs')
          else do
          (e, psU) <- makePatternsU nsU ppsU
          let alts = groupBy ((==) `on` (\(pU,_,_) -> pU)) (zip3 psU psR' cs')
              alts' = map (\ralts@((pU,_,_):_) ->
                             let ralts' = map (\(_,pR,(e1,e2)) -> (pR,e1,e2)) ralts
                             in (pU, C.RCase (C.Var nR) ralts')) alts
          return $ C.Case e alts'
    return $ foldr C.Abs body ns
  where
    makePatternsU :: MonadDesugar m => [Name] -> [[S.LPat 'TypeCheck]] -> m (C.Exp Name, [C.Pat Name])
    makePatternsU ns pps = do
      pps' <- mapM (mapM desugarPat) pps
      return (makeTupleExpC (map C.Var ns), map makeTuplePatC pps')


convertClauseU :: MonadDesugar m => S.Clause 'TypeCheck -> m (C.Exp Name)
convertClauseU (S.Clause body ws Nothing) =
  desugarExp (noLoc $ S.Let ws body)
convertClauseU _ = error "Cannot happen."

convertClauseR :: MonadDesugar m => S.Clause 'TypeCheck -> m (C.Exp Name, C.Exp Name)
convertClauseR (S.Clause body ws wi) = do
  body' <- desugarExp (noLoc $ S.Let ws body)
  we' <- case wi of
           Just e  -> desugarExp e
           Nothing -> generateWithExp body'
  return (body', we')

generateWithExp :: MonadDesugar m => C.Exp Name -> m (C.Exp Name)
generateWithExp _ = withNewName $ \n ->
  return $ C.Abs n $ C.Con conTrue []

desugarPat :: MonadDesugar m => S.LPat 'TypeCheck -> m (C.Pat Name)
desugarPat = desugarPPat . snd . S.unLPat

desugarPPat :: MonadDesugar m => S.LPPat 'TypeCheck -> m (C.Pat Name)
desugarPPat = go . unLoc
  where
    go (S.PVar (x, _ty))    = return $ C.PVar x
    go (S.PLit l)           = return $ C.PLit l
    go (S.PCon (c, _ty) ps) = C.PCon c <$> mapM desugarPPat ps
    go _                    = error "desugarPat: Cannot happen."

desugarTopDecls ::
  MonadDesugar m => S.Decls 'TypeCheck (S.LDecl 'TypeCheck) -> m (C.Bind Name)
desugarTopDecls (S.Decls v _) = absurd v
desugarTopDecls (S.HDecls _ bss) = do
  let defs = [ (n, ty, pcs) | bs <- bss, Loc _ (S.DDef (n, ty) pcs) <- bs ]
  forM defs $ \(n, ty, pcs) -> do
    e <- desugarRHS pcs
    return (n, ty, e)

