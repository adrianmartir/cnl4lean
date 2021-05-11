
import Lean

/- We use our own proposition type in order to be able to use our own
implementation of `True` that gets automatically reduced when applying
logical operators. This is absolutely essential for the generated
lemmata to be readable -/
namespace CNL4Lean

open Lean hiding Expr
open Lean.Meta

inductive Proposition where
  | expr: Lean.Expr -> Proposition
  | top: Proposition

def Proposition.run (f : Lean.Expr -> α) (p: Proposition) : α :=
  match p with
  | expr e => f e
  | top => f (mkConst `True)
