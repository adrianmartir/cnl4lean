
import Lean

-- Some utilities for manipulating lean expressions
namespace ReadableLean

open Lean hiding Expr
open Lean.Meta

/- We use our own proposition type in order to be able to use our own
implementation of `True` that gets automatically reduced when applying
logical operators. This is absolutely essential for the generated
lemmata to be readable -/
inductive Proposition where
  | expr: Lean.Expr -> Proposition
  | top: Proposition

-- Simple unifying application.
-- * Doesn't deal with different argument types
-- * No coercions
-- * No propagating expected type for smarter coercions
-- * No synthetic metavariables
-- The lean application implementation is in `Elab/App.lean` and it has
-- **a lot** more features.
def app (f: Lean.Expr) (arg: Lean.Expr) : MetaM Lean.Expr := do
  let fType <- inferType f
  let dom <- fType.bindingDomain!
  let type <- inferType arg
  unless <- isDefEq dom type do throwError "Expected type {dom}, got {type}"
  mkApp f arg

-- Copied from `AppBuilder.lean`. Instantiates universe parameters.
def mkFun (constName : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType := cinfo.instantiateTypeLevelParams us
  return (f, fType)

def appN (ident: Name) (args: Array Lean.Expr) : MetaM Lean.Expr := do
  let f <- mkFun ident
  args.foldlM (fun f arg => app f arg) f.1


def mkExistsFVars' (fvars: Array Lean.Expr) (e: Lean.Expr) : MetaM Lean.Expr :=
  fvars.foldrM (fun fvar acc => do
    let typeFamily <- mkLambdaFVars #[fvar] acc
    -- We use `mkAppM` since we need to instantiate an implicit argument.
    mkAppM `Exists #[typeFamily]) e

namespace Proposition

instance : Inhabited Proposition where
  default := top

def run  (p: Proposition) : Lean.Expr :=
  match p with
  | expr e => e
  | top => mkConst `True

def not : Proposition -> MetaM Proposition
  | expr p => expr <$> appN `Not #[p]
  | top => expr <$> mkConst `False

def and : Proposition -> Proposition -> MetaM Proposition
  | expr p1, expr p2 => expr <$> appN `And #[p1, p2]
  | top, p => p
  | p, top => p

def or : Proposition -> Proposition -> MetaM Proposition
  | top, _ => top
  | _, top => top
  | expr p1, expr p2 => expr <$> appN `Or #[p1, p2]

def andN (ps: Array Proposition) : MetaM Proposition := do
  ps.foldlM and top

def implies : Proposition -> Proposition -> MetaM Proposition
  | _, top => top
  | top, p => p
  | expr p1, expr p2 => expr <$> appN `implies #[p1, p2]

def iff : Proposition -> Proposition -> MetaM Proposition
  | top, top => top
  | top, p => p
  | p, top => p
  | expr p1, expr p2 => expr <$> appN `Iff #[p1, p2]


def xor : Proposition -> Proposition -> MetaM Proposition
  | top, top => expr <$> mkConst `False
  | top, p => not p
  | p, top => not p
  | expr p1, expr p2 => do
    let p <- appN (<- resolveGlobalConstNoOverload `xor) #[p1, p2]
    expr p

def nor : Proposition -> Proposition -> MetaM Proposition
  | top, _ => expr <$> mkConst `False
  | _, top => expr <$> mkConst `False
  | expr p1, expr p2 => do
    let p <- appN (<- resolveGlobalConstNoOverload `nor) #[p1, p2]
    expr p

def mkExistsFVars (fvars: Array Lean.Expr) (p: Proposition) : MetaM Proposition :=
   expr <$> mkExistsFVars' fvars p.run

def mkForallFVars (fvars: Array Lean.Expr) (p: Proposition) : MetaM Proposition := match p with
  | expr e => expr <$> Meta.mkForallFVars fvars e
  | top => top

end Proposition
