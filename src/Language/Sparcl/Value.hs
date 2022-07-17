module Language.Sparcl.Value where

import           Language.Sparcl.Pretty    as D

import           Control.DeepSeq
import qualified Data.Map                  as M

import           Language.Sparcl.Core.Syntax
import           Language.Sparcl.Exception
import           Language.Sparcl.Literal
import           Language.Sparcl.Name

data Value = VCon !Name ![Value]
           | VLit !Literal
           | VFun !(Env, Name, Exp Name)
           | VOp  !(Value -> Value) -- Builtin operator
           | VLift !(Value -> Value) (Value -> Value)

type ValueTable = M.Map Name Value
type Env = M.Map Name Value

instance NFData Value where
  rnf (VCon c vs) = rnf (c, vs)
  rnf (VLit l)    = rnf l
  rnf (VFun _)    = ()

instance Pretty Value where
  pprPrec _ (VCon c []) = ppr c
  pprPrec k (VCon c vs) = parensIf (k > 9) $
    ppr c D.<+> D.hsep [ pprPrec 10 v | v <- vs ]

  pprPrec _ (VLit l) = ppr l
  pprPrec _ (VFun _) = D.text "<function>"

-- type Eval = ReaderT Int (Either String)

extendsEnv :: [(Name, Value)] -> Env -> Env
extendsEnv nvs env = foldr (uncurry extendEnv) env nvs

lookupEnv :: Name -> Env -> Maybe Value
lookupEnv = M.lookup

lookupEnvStrict :: Name -> Env -> Value
lookupEnvStrict n env = case M.lookup n env of
  Nothing -> rtError $ D.text "Undefined variable:" D.<+> ppr n
  Just v  -> v

removeEnv :: Name -> Env -> Env
removeEnv = M.delete

removesEnv :: [Name] -> Env -> Env
removesEnv xs env = foldl (flip removeEnv) env xs

singletonEnv :: Name -> Value -> Env
singletonEnv = M.singleton

extendEnv :: Name -> Value -> Env -> Env
extendEnv = M.insert

unionEnv :: Env -> Env -> Env
unionEnv = M.union

emptyEnv :: Env
emptyEnv = M.empty

pprEnv :: Env -> Doc
pprEnv env =
  D.sep [ ppr k D.<+> D.text "=" D.<+> ppr v
        | (k, v) <- M.toList env ]
