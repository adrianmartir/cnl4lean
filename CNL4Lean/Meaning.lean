
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
-- When building expressions, these identifiers are assumed to be in the environment.
-- They are added to the environment by imports and definitions.
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
  | Expr'.symbol symb => do
    -- let args <- (NonEmpty.toArray args).sequenceMap interpretExpr
    -- Patterns add indirection.
    -- mkAppM (getSymbIdentifier symb) args
    -- getSymbIdentifier symb
    sorry
  | Expr'.app _ _ => sorry

mutual
  -- Patterns add indirection.
  partial def interpretFun (fun' : Fun) : MetaM Expr := match fun' with
    | Fun.lexicalPhrase lexicalPhrase args => do
      let args <- (List.toArray args).sequenceMap interpretTerm
      mkAppM (getSgPlIdentifier lexicalPhrase) args

  partial def interpretTerm (term : Term) : MetaM Expr := match term with
    | Term.expr e => interpretExpr e
    | Term.function f => interpretFun f
end

private def interpretApp (ident: Name) (args: List Term) : MetaM Expr := do
  let args <- (List.toArray args).sequenceMap interpretTerm
  mkAppM ident args

def interpretNoun (noun: Noun Term) : MetaM Expr := 
  interpretApp (getSgPlIdentifier noun.lexicalPhrase) noun.arguments
  -- Maybe ensure that the result is `?m -> Prop`?

def interpretAdj (adj: Adj Term) : MetaM Expr := 
  interpretApp sorry adj.arguments

def interpretVerb (verb: Verb Term) : MetaM Expr := 
  interpretApp sorry verb.arguments

def negatePredicate (pred : Expr) : Expr := sorry

def interpretVerbPhrase (verbPhrase : VerbPhrase) : MetaM Expr := match verbPhrase with
  | VerbPhrase.verb verb => interpretVerb verb
  | VerbPhrase.adj adj => interpretAdj adj
  | VerbPhrase.verbNot verb => do
    let pred <- interpretVerb verb
    negatePredicate pred
  | VerbPhrase.adjNot adj => do
    let pred <- interpretAdj adj
    negatePredicate pred

def interpretAdjL (adj: AdjL) : MetaM Expr :=
  interpretAdj (Adj.mk adj.lexicalPhrase adj.arguments)

def interpretAdjR (adj: AdjR) : MetaM Expr := sorry

def interpretNounPhrase (nounPhrase : NounPhrase) : Int := sorry

def interpretAsm (asm : Asm) : MetaM Int := sorry
-- 1) Simply add the variable to the local context (without type) (say, `x : ?m`).
-- 2) Run `MetaM` in that context in order to parse the statement/expression/...


-- This should yield a context of declarations.

def interpretPara (p: Para) : MetaM Unit := sorry
