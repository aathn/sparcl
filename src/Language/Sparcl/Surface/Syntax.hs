{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Language.Sparcl.Surface.Syntax (
  XId, XTId, LTy, Ty(..), TConstraint(..),

  isTyArr, decomposeArrTy, decomposeTyCon,

  LPat, Pat(..),
  LExp, Exp(..), Clause(..),


  Prec(..), Assoc(..),
  Decls(..), XDecls, XHDecls, LDecl, Decl(..), CDecl(..), TopDecl(..),

  Module(..), Export, Import(..),

  module Language.Sparcl.Pass,
  module Language.Sparcl.FreeTyVars,
  module Language.Sparcl.Literal,
  module Language.Sparcl.Multiplicity,
  module Language.Sparcl.Name
  ) where

import           Language.Sparcl.SrcLoc

import           Language.Sparcl.Pretty       as D

-- Surface Syntax

import           Language.Sparcl.FreeTyVars
import           Language.Sparcl.Literal
import           Language.Sparcl.Multiplicity
import           Language.Sparcl.Name
import           Language.Sparcl.Pass

import qualified Language.Sparcl.Typing.Type  as Typing

import           Data.Kind
import           Data.Void

import           Data.Typeable

type LTy p = Loc (Ty p) -- located types (not linear)

{-
The following would be a bit generous definition, but
we want to allow types that are parameterized by multiplicity.
-}

data Ty (p :: Pass)
  = TVar    !(XTId p)
  | TCon    !(XTId p) ![LTy p]
  | TForall !(XTId p) !(LTy p)
  | TQual   ![TConstraint p] !(LTy p)
  | TMult   !Multiplicity


-- TODO: Maybe, we should add Eq or Ord later.
data TConstraint p = MSub ![LTy p] ![LTy p] -- max p1 ... pn <= max q1 ... qm
                   | TyEq !(LTy p) !(LTy p) -- t1 ~ t2



instance (Ord a, a ~ XTId p) => FreeTyVars (LTy p) a where
  foldMapVars f b t = foldMapVars f b (unLoc t)

instance (Ord a, a ~ XTId p) => FreeTyVars (Ty p) a where
  foldMapVars f _ (TVar x)      = f x
  foldMapVars f b (TCon _ ts)   = foldMapVars f b ts
  foldMapVars f b (TForall x t) = b x $ foldMapVars f b t
  foldMapVars f b (TQual cs t)  = foldMapVars f b cs <> foldMapVars f b t
  foldMapVars _ _ (TMult _)     = mempty

instance (Ord a, a ~ XTId p) => FreeTyVars (TConstraint p) a where
  foldMapVars f b (MSub ms1 ms2) = foldMapVars f b ms1 <> foldMapVars f b ms2
  foldMapVars f b (TyEq t1 t2)   = foldMapVars f b t1  <> foldMapVars f b t2




type family XTId (p :: Pass) where
  XTId 'Parsing = SurfaceName
  XTId _        = Name

instance AllPretty p => Pretty (TConstraint p) where
  ppr (TyEq t1 t2)      = ppr t1 <+> text "~" <+> ppr t2
  ppr (MSub p1 p2)      = pprMs p1 <+> text "<=" <+> pprMs p2
    where
      pprMs []     = ppr One -- unit of multiplication
      pprMs [x]    = ppr x
      pprMs (x:xs) = go x xs

      go x []     = ppr x
      go x (y:ys) = ppr x <> text "*" <> go y ys



isTyArr :: forall p. Typeable p => Proxy p -> XTId p -> Bool
isTyArr _ n =
  case eqT @p @'Parsing of
    Just Refl -> n == BuiltIn nameTyArr
    Nothing ->
      case eqT @p @'Renaming of
        Just Refl -> n == nameTyArr
        _         -> False


decomposeArrTy :: forall p. Typeable p => LTy p -> ([(LTy p, LTy p)], LTy p)
decomposeArrTy (unLoc -> TCon c [m, t2, t3])
  | isTyArr @p Proxy c =
      let (args, ret) = decomposeArrTy t3
      in ( (t2,m):args, ret )
decomposeArrTy ty = ([], ty)

decomposeTyCon :: Eq (XTId p) => XTId p -> LTy p -> Maybe [LTy p]
decomposeTyCon c (unLoc -> TCon c' ts) | c == c' = Just ts
decomposeTyCon _ _                     = Nothing


instance AllPretty p => Pretty (Ty p) where
  pprPrec _ (TVar n) = ppr n
  pprPrec k (TCon c [m,t1,t2])
    | isTyArr (Proxy :: Proxy p) c =
        let arr = case unLoc m of
                    TMult Omega -> line <> text "->"
                    TMult One   -> line <> text "-o"
                    _ -> text " " <> text "#" <+> ppr m D.<$> text "->"
        in parensIf (k > 0) $ D.group $ pprPrec 1 t1 <> arr <+> pprPrec 0 t2
  pprPrec k (TCon c ts) = parensIf  (k > 1) $ ppr c D.<+> D.hsep (map (pprPrec 2) ts)

  pprPrec k (TQual cs t) = parensIf (k > 0) $ align $
    parens (hsep $ D.punctuate comma $ map ppr cs) D.<$> D.text "=>" D.<+> pprPrec 0 t
  pprPrec k ty@(TForall _ _) =
    let (ns, t) = gatherVars [] ty
    in parensIf (k > 0) $ group $ align $ nest 2 $
       D.text "forall" D.<+> hsep (map ppr ns) <> text "." D.<$> pprPrec 0 t
    where
      gatherVars ns (TQual [] t)  = gatherVars ns (unLoc t)
      gatherVars ns (TForall m t) = gatherVars (m:ns) (unLoc t)
      gatherVars ns t             = (reverse ns, t)
  pprPrec _ (TMult m) = ppr m

instance AllPretty p => Pretty (Loc (Ty p)) where
  pprPrec k = pprPrec k . unLoc

type LExp p = Loc (Exp p)

type family XId (p :: Pass) = q | q -> p where
  XId 'Parsing   = SurfaceName
  XId 'Renaming  = Name
  XId 'TypeCheck = (Name, Typing.Ty)


class QueryName p where
  checkTuple :: XId p -> Maybe Int

instance QueryName 'Parsing where
  checkTuple (BuiltIn n) = checkTuple n
  checkTuple _           = Nothing

instance QueryName 'Renaming where
  checkTuple (Original _ (System (NTuple n)) _) = Just n
  checkTuple _                                  = Nothing

instance QueryName 'TypeCheck where
  checkTuple (n, _) = checkTuple n


type ForallX (f :: Type -> Constraint) p = (f (XId p), f (XTId p))
type AllPretty p = (ForallX Pretty p, QueryName p, Typeable p)

-- TODO: add "if" expression
data Exp p
  = Lit !Literal
  | Var !(XId p)
  | App !(LExp p) !(LExp p)
  | Abs ![LPat p] !(LExp p)
  | Con !(XId p) ![LExp p]
  | Case !(LExp p) ![ (LPat p, Clause p) ]
  | Lift
  | Sig  !(LExp p) !(LTy p)
  | Let  !(Decls p (LDecl p)) !(LExp p)
  | Let1 !(LPat p) !(LExp p)  !(LExp p)

  | Parens !(LExp p) -- for operators
  | Op  !(XId p) !(LExp p) !(LExp p)

  | FApp !(LExp p) !(LExp p)
  | BApp !(LExp p) !(LExp p)
  | RPin !(LPat p) !(LExp p) !(LExp p)


instance AllPretty p => Pretty (LExp p) where
  pprPrec k = pprPrec k . unLoc

instance AllPretty p => Pretty (Exp p) where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $
    D.text "\\" D.<> D.hsep (map ppr x) D.<+> D.text "->" D.<+> D.align (D.nest 2 (pprPrec 0 e))

  pprPrec _ (Con c []) = ppr c
  pprPrec k (Con c es) = parensIf (k > 0) $
    ppr c D.<+> D.hsep (map (pprPrec 1) es)

  pprPrec k (Case e ps) = parensIf (k > 0) $
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.</>
    D.vcat (map pprPs ps) D.</>
    D.text "end"
    where
      pprPs (p, c) = D.text "|" D.<+>
                     D.align (pprPrec 1 p D.<+> D.text "->" D.<+> D.nest 2 (ppr c))

  pprPrec _ Lift   = text "lift"

  pprPrec _ (Parens e) = D.parens (pprPrec 0 e)
  pprPrec k (Op q e1 e2) = parensIf (k > 8) $
    pprPrec 8 e1 D.<+> ppr q D.<+> pprPrec 9 e2

  pprPrec k (Sig e t) = parensIf (k > 0) $
    pprPrec 0 e D.<+> D.colon D.<+> ppr t

  pprPrec k (Let decls e) = parensIf (k > 0) $
    D.align $
     D.text "let" D.<+> D.align (pprDecls decls) D.</>
     D.text "in" D.<+> pprPrec 0 e

    where
      pprDecls (Decls _ ds)   = vcat $ map ppr ds
      pprDecls (HDecls _ dss) = vcat $ map (vcat . map ppr) dss

  pprPrec k (Let1 p e1 e2) = parensIf (k > 0) $ D.align $
    D.text "let" D.<+> D.align (ppr p <+> text "<-" <+> ppr e1 <+> D.text "in") D.</>
    pprPrec 0 e2

  pprPrec k (FApp e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> D.text "|>" D.<+> pprPrec 10 e2

  pprPrec k (BApp e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> D.text "<|" D.<+> pprPrec 10 e2

  pprPrec k (RPin p e1 e2) = parensIf (k > 0) $ D.align $
    D.text "pin" D.<+> D.align (ppr p <+> text "<-" <+> ppr e1 <+> D.text "in") D.</>
    pprPrec 0 e2



type LPat p = Loc (Pat p)
data Pat p = PVar !(XId p)
           | PCon !(XId p) ![LPat p]
           | PWild !(XPWild p) -- PWild x will be treated as !x after renaming
         -- TODO: Add literal pattern
--   deriving Show

type family XPWild (p :: Pass) where
  XPWild 'Parsing   = ()
  XPWild 'Renaming  = XId 'Renaming
  XPWild 'TypeCheck = XId 'TypeCheck

instance AllPretty p => Pretty (Loc (Pat p)) where
  pprPrec k = pprPrec k . unLoc

instance AllPretty p => Pretty (Pat p) where
  pprPrec _ (PVar n) = ppr n

  pprPrec _ (PCon c ps)
    | Just n <- checkTuple c,  n == length ps =
        D.parens $ D.hsep $ D.punctuate D.comma $ map (pprPrec 0) ps

  pprPrec _ (PCon c []) = ppr c
  pprPrec k (PCon c ps) = parensIf (k > 0) $
    ppr c D.<+> D.hsep (map (pprPrec 1) ps)

  pprPrec _ (PWild _) = D.text "_"

data Clause p = Clause { body :: LExp p, whereClause :: Decls p (LDecl p), withExp :: Maybe (LExp p) }
--  deriving Show

instance AllPretty p => Pretty (Clause p) where
  ppr (Clause e decls w) =
    ppr e D.<+> (case w of
                   Nothing -> D.empty
                   Just e' -> D.text "with" D.<+> D.align (ppr e'))
    D.<> pprDecls decls
    where
      pprDecls (Decls  _ ds) = pprWhere ds
      pprDecls (HDecls _ ds) = pprWhere (concat ds)
      pprWhere ds =
        case ds of
          [] -> D.empty
          _  ->
            D.nest 2 (D.line D.<> D.nest 2 (D.text "where" D.</>
                                            D.align (D.vcat $ map ppr ds)) D.</> D.text "end")


newtype Prec  = Prec Int
  deriving (Eq, Ord, Show)

instance Pretty Prec where
  ppr (Prec k) = D.int k

instance Bounded Prec where
  minBound = Prec 0
  maxBound = Prec maxBound

instance Enum Prec where
  toEnum = Prec
  fromEnum (Prec n) = n

data Assoc = L | R | N
  deriving (Eq, Ord, Show)

instance Pretty Assoc where
  ppr L = D.text "left"
  ppr R = D.text "right"
  ppr N = D.empty

type LDecl p = Loc (Decl p)

data CDecl p
  = NormalC !(XId p)  -- constructor name
            ![LTy p]  -- constructor argument

instance AllPretty p => Pretty (Loc (CDecl p)) where
  ppr (Loc l d) =
    D.text "{-" D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d

instance AllPretty p => Pretty (CDecl p) where
  ppr (NormalC c []) = ppr c
  ppr (NormalC c args) =
    ppr c D.<+> D.hsep [ pprPrec 1 a | a <- args ]

data Decls p x = Decls  (XDecls p)  [x]
               | HDecls (XHDecls p) [[x]]

instance (Pretty x, AllPretty p) => Pretty (Decls p x) where
  ppr (Decls  _ ds)  = vcat (map ppr ds)
  ppr (HDecls _ dss) = vcat (map (vcat . map ppr) dss)

type family XDecls p where
  XDecls 'Parsing = ()
  XDecls _        = Void

type family XHDecls p where
  XHDecls 'Parsing  = Void
  XHDecls 'Renaming = ()
  XHDecls 'TypeCheck = ()

data TopDecl p
  = DDecl !(Decl p)
  | DData !(XId p) ![XId p] ![Loc (CDecl p)]   -- data type declaration
  | DType !(XId p) ![XId p] !(LTy p)

data Decl p
  = DDef !(XId p) ![ ([LPat p],  Clause p) ]
  | DSig !(XId p) !(LTy p)
  | DFixity !(XId p) !Prec !Assoc -- TODO: will be replaced with "DDefOp"
  -- | DMutual [LDecl]


instance AllPretty p => Pretty (Loc (TopDecl p)) where
  ppr (Loc l d) =
    D.text "{- " D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d

  pprList _ ds =
    D.vsep (map ppr ds)


instance AllPretty p => Pretty (TopDecl p) where
  ppr (DData t targs constrs) =
    D.hsep [D.text "data", ppr t, D.align $ D.hsep (map ppr targs)] D.<>
    D.nest 2 (D.line D.<> D.text "=" D.<+> D.group (pprCs constrs))
    where
      pprCs []     = D.empty
      pprCs [c]    = ppr c
      pprCs (c:cs) = ppr c D.<$> D.text "|" D.<+> pprCs cs

  ppr (DType t targs ty) =
    D.hsep [D.text "type", ppr t, D.align $ D.hsep (map ppr targs),
            D.align (ppr ty)]

  ppr (DDecl d) = ppr d

instance AllPretty p => Pretty (Decl p) where
  ppr (DDef n pcs) =
    D.text "def" D.<+> ppr n D.<+>
    D.align (D.nest (-2) $
            D.hcat $ D.punctuate (D.line D.<> D.text "|" D.<> D.space)
                                 (map pprPC pcs))
    where
      pprPC (ps, c) =
        D.align $
          D.hsep (map (pprPrec 1) ps) D.<+> D.text "=" D.<+> ppr c

  ppr (DSig n t) =
    D.text "sig" D.<+> ppr n D.<+> D.colon D.<+> ppr t

  ppr (DFixity n k a) =
    D.text "fixity" D.<+> ppr n D.<+> ppr k D.<+> ppr a



  -- ppr (DMutual ds) =
  --   D.text "mutual" D.<+> D.semiBraces (map ppr ds)

  pprList _ ds =
    D.vsep (map ppr ds)

instance AllPretty p => Pretty (Loc (Decl p)) where
  ppr (Loc l d) =
    D.text "{- " D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d

  pprList _ ds =
    D.vsep (map ppr ds)


data Module p
  = Module ModuleName (Maybe [Export p]) [Import p] (Decls p (Loc (TopDecl p)))

instance AllPretty p => Pretty (Module p) where
  ppr (Module m es is ds) =
    hsep [ text "module" , ppr m,
           case es of
             Nothing -> empty
             Just vs -> parens (hsep $ D.punctuate comma $ map (ppr . unLoc) vs),
           text "where" ]
    <> line <> vcat (map ppr is)
    <> line <> ppr ds


type Export p = Loc (XId p)
data Import p = Import { importModuleName :: !ModuleName, importingNames :: !(Maybe [Loc (XId p)]) }

instance AllPretty p => Pretty (Import p) where
  ppr (Import m is) =
    text "import" <+> ppr m <+>
    (case is of
       Nothing -> D.empty
       Just ns -> parens (hsep $ D.punctuate comma $ map (ppr . unLoc) ns))

