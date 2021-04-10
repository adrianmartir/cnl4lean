
import CNL4Lean.Grammar
import Lean
-- The goal is to create a dummy file and to write all the natural constructs to it.
-- Then, can I somehow make the environment into an `.olean` file? I am not sure how
-- this would work.

namespace CNL4Lean

open Lean
open Lean.Meta

-- In this module I use the `MetaM` monad as a logic framework that exposes leans 
-- internals. I decided against using the `TermElabM` monad, because it contains many
-- lean-specific mechanisms, like macro expansion and debugging. Most of the instances
-- for `TermElabM` contain lean-specific `Syntax` objects or macro stuff.

-- In any case, I will probably need to read the `TermElabM` monad source code and copy
-- some of the patterns I see there.

-- For instance, I will need to learn
-- * How to create metavariables for types to be inferred (For now I could make all types explicit)
-- * Namespacing and modules (this seems to be quite confusing)

-- It might be worth looking at `elabOpen` and `elabTerm` in `Elab/Term.lean`.

def interpretVar (var: VarSymbol) : Expr := match var with
  -- `mkFVar` might really be way to low level. Don't we need to somehow specify the type
  -- of it?
  | VarSymbol.namedVar name => Name.mkSimple name |> mkFVar
  | _ => sorry -- I think this rarely occurs

-- The identifier should be stored in the symbol datatype and in the vocabulary
-- It should be possible to look up these identifiers in the environment.
def getSymbIdentifier (var: Symbol) : Name := sorry

def getSgPlIdentifier (sgpl: SgPl) : Name := sorry

-- Does the have to get registered at some point? Yes. They are expected to be in the
-- local context from which the `MetaM` monad has been invoked. For instance, we may
-- have some assumptions in a lemma. Or in quantifiers(?). Then we somehow need to launch
-- the `MetaM` monad again in that context.
partial def interpretExpr (expr: Expr') : MetaM Expr := match expr with
  | Expr'.var var => interpretVar var
  | Expr'.int (Int.ofNat n) => mkNatLit n
  | Expr'.int _ => panic! "Integer literals can't be negative."
  -- The identifiers should be queried from the pattern definition tex labels.
  -- We use `mkAppM` in order to enable stuff like typeclasses and implicit arguments
  -- (at least theoretically)
  | Expr'.symbol symb args => do
    let args <- (NonEmpty.toArray args).sequenceMap interpretExpr
    -- Patterns add indirection.
    mkAppM (getSymbIdentifier symb) args

mutual
  -- Patterns add indirection.
  partial def interpretFun (fun' : Fun) : MetaM Expr := match fun' with
    | Fun.lexicalPhrase sgpl args => do
      let args <- (List.toArray args).sequenceMap interpretTerm
      mkAppM (getSgPlIdentifier sgpl) args

  partial def interpretTerm (term : Term) : MetaM Expr := match term with
    | Term.expr e => interpretExpr e
    | Term.function f => interpretFun f
end

def interpretAsm (asm : Asm) : MetaM Int := sorry
-- 1) Simply add the variable to the local context (without type) (say, `x : ?m`).
-- 2) Run `MetaM` in that context in order to parse the statement/expression/...


-- This should yield a context of declarations.

def interpretPara (p: Para) : MetaM Unit := sorry
