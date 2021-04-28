
import CNL4Lean.Grammar
import Lean
-- The goal is to create a dummy file and to write all the natural constructs to it.
-- Then, can I somehow make the environment into an `.olean` file? I am not sure how
-- this would work.

namespace CNL4Lean

open Lean
open Lean.Meta

-- In this module I use the `MetaM` monad as a logic framework that exposes leans
-- internals. I decided against using the `Grammar.TermElabM` monad, because it contains many
-- lean-specific mechanisms, like macro expansion and debugging. Most of the instances
-- for `Grammar.TermElabM` contain lean-specific `Syntax` objects or macro stuff.

-- In any case, I will probably need to read the `Grammar.TermElabM` monad source code and copy
-- some of the patterns I see there.

-- For instance, I will need to learn
-- * How to create metavariables for types to be inferred (For now I could make all types explicit)
-- * Namespacing and modules (this seems to be quite confusing)

-- It might be worth looking at `elabOpen` and `elabGrammar.Term` in `Elab/Grammar.Term.lean`.

class Means (α: Type) (β: Type) where
  interpret : α -> MetaM β

open Means

instance : Means Grammar.Pattern Name where
  interpret pat :=
    pat.foldl (fun acc next => acc ++ toString next) ""
      |> Name.mkSimple

instance : Means Grammar.SgPl Name where
  interpret pat := interpret pat.sg

instance : Means Grammar.VarSymbol Name where
  interpret (var: Grammar.VarSymbol) : Name := match var with
  -- `mkFVar` might really be way to low level. Note that when
  -- first declaring the variable, it needs to have a type and
  -- then needs to get added to the context.
  | Grammar.VarSymbol.namedVar name => Name.mkSimple name
  | _ => sorry -- I think this rarely occurs

private partial def interpretExpr
  | Grammar.Expr.var var => mkFVar <$> interpret var
  | Grammar.Expr.int (Int.ofNat n) => mkNatLit n
  | Grammar.Expr.int _ => panic! "Integer literals can't be negative."
  -- The identifiers should be queried from the pattern definition tex labels.
  -- We use `mkAppM` in order to enable stuff like typeclasses and implicit arguments
  -- (at least theoretically)
  | Grammar.Expr.mixfix symb args => do
    let args <- args.mapM interpretExpr
    -- Patterns add indirection.
    mkAppM sorry args
  | Grammar.Expr.app _ _ => sorry
    -- We want a dumbed-down application here(no implicits).
    -- Typeclasses should be merely a **notational** construct - which in
    -- CNL has gets handled in *patterns*. This should be only for doing
    -- higher order logic.
  | _ => sorry

instance : Means Grammar.Expr Expr := mk interpretExpr


private def interpretApp [a: Means α Name] [b: Means β Expr] (ident: α) (args: Array β) : MetaM Expr := do
  let args <- args.mapM interpret
  let ident <- interpret ident
  mkAppM ident args

mutual
  -- Patterns add indirection.
  partial def interpretFun (fun' : Grammar.Fun) : MetaM Expr := match fun' with
    | Grammar.Fun.mk lexicalPhrase args =>
        interpretApp (b := mk interpretTerm) lexicalPhrase args

  partial def interpretTerm (term : Grammar.Term) : MetaM Expr := match term with
    | Grammar.Term.expr e => interpretExpr e
    | Grammar.Term.function f => interpretFun f
end

instance : Means Grammar.Fun Expr := mk interpretFun
instance : Means Grammar.Term Expr := mk interpretTerm


instance [Means α Expr]: Means (Grammar.Noun α) Expr where
  interpret
    | Grammar.Noun.mk sgPl args => interpretApp sgPl args
    -- Maybe ensure that the result is `?m -> Prop`?

instance [Means α Expr]: Means (Grammar.Adj α) Expr where
  interpret
    | Grammar.Adj.mk pat args => interpretApp pat args

instance [Means α Expr]: Means (Grammar.Verb α) Expr where
  interpret
    | Grammar.Verb.mk sgPl args => interpretApp sgPl args

-- `negate : (α -> Prop) -> (α -> Prop)` is in `Init.lean`!
-- Does this work without `mkAppM`?
def negate (e: Expr) : MetaM Expr := mkAppM `negate #[e]

def conjunction (p1: Expr) (p2: Expr) : MetaM Expr :=
  mkAppM `conjunction #[p1, p2]

def disjunction (p1: Expr) (p2: Expr) : MetaM Expr :=
  mkAppM `disjunction #[p1, p2]

instance : Means Grammar.VerbPhrase Expr where
  interpret
    | Grammar.VerbPhrase.verb verb => interpret verb
    | Grammar.VerbPhrase.adj adj => interpret adj
    | Grammar.VerbPhrase.verbNot verb => interpret verb >>= negate
    | Grammar.VerbPhrase.adjNot adj => interpret adj >>= negate

instance : Means Grammar.AdjL Expr where
  interpret
    | Grammar.AdjL.mk pat args => interpretApp pat args

instance : Means Grammar.AdjR Expr where
  interpret
    | Grammar.AdjR.adjR pat args => interpretApp pat args
    | Grammar.AdjR.attrRThat verbPhrase => interpret verbPhrase

mutual
private partial def interpretNP : Grammar.NounPhrase -> MetaM Expr
  | Grammar.NounPhrase.mk adjL noun varSymb? adjR stmt? => sorry
  -- This should be an `and` and it should also abstract `stmt?` by
  -- using `varSymb?`.

private partial def interpretNPVars : Grammar.NounPhraseVars -> MetaM Expr
  | Grammar.NounPhraseVars.mk adjL noun varSymbs adjR stmt? => sorry
  -- This should be an `and`

-- A simplified version of `Elab.Term.elabForall`
private partial def interpretQP : Grammar.QuantPhrase -> MetaM Expr
  | Grammar.QuantPhrase.mk q np => do
      let expr <- interpretNPVars np
      let vars: Array Name <- np.vars.mapM interpret
      -- `Elab.Term.ensureType` also tries to coerce into a type, but
      -- lets not overcomplicate things for now
      if <- isProp expr then
        sorry
      else
        throwError "proposition expected"

private partial def interpretStmt : Grammar.Stmt -> MetaM Expr := sorry
end

def interpretAsm (asm : Grammar.Asm) : MetaM Int := sorry
-- 1) Simply add the variable to the local context (without type) (say, `x : ?m`).
-- 2) Run `MetaM` in that context in order to parse the statement/expression/...


-- This should yield a context of declarations.

def interpretPara (p: Grammar.Para) : MetaM Unit := sorry
