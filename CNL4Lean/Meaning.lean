
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

class Means (α: Type) (β: Type) [Inhabited β] where
  interpret : α -> β

open Means

-- The following two definitions are used in order to write partial
-- instances of `Means`, since currently instances and `partial`
-- don't get along.
instance [Inhabited β]: Inhabited (Means α β) where
  default := mk fun x => arbitrary

def interpret' [Inhabited β] (means : Means α β) := @interpret α β _ means


instance : Means Grammar.Pattern Name where
  interpret pat :=
    pat.foldl (fun acc next => acc ++ toString next) ""
      |> Name.mkSimple

instance : Means Grammar.SgPl Name where
  interpret pat := interpret pat.sg

instance : Means Grammar.VarSymbol Name where
  interpret (var: Grammar.VarSymbol) : Name := match var with
  | Grammar.VarSymbol.namedVar name => Name.mkSimple name
  | _ => sorry -- I think this rarely occurs


-- Simple unifying application.
-- * Doesn't deal with different argument types
-- * No coercions
-- * No propagating expected type for smarter coercions
-- * No synthetic metavariables
-- The lean application implementation is in `Elab/App.lean` and it has
-- **a lot** more features.
private def app (f: Expr) (arg: Expr) : MetaM Expr := do
  let fType <- inferType f
  let dom <- fType.bindingDomain!
  let type <- inferType arg
  unless <- isDefEq dom type do throwError "Expected type {dom}, got {type}"
  mkApp f arg

-- Copied from `AppBuilder.lean`. Instantiates universe parameters.
private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType := cinfo.instantiateTypeLevelParams us
  return (f, fType)

private def appN (ident: Name) (args: Array Expr) : MetaM Expr := do
  let f <- mkFun ident
  args.foldlM (fun f arg => app f arg) f.1


private def interpretApp [m1: Means α Name] [m2: Means β (MetaM Expr)] (ident: α) (args: Array β) : MetaM Expr := do
  let args <- args.mapM interpret
  appN (interpret ident) args


partial instance meansE: Means Grammar.Expr (MetaM Expr) where
  interpret
  | Grammar.Expr.var var => mkFVar <| interpret var
  | Grammar.Expr.int (Int.ofNat n) => mkNatLit n
  | Grammar.Expr.int _ => panic! "Integer literals can't be negative."
  -- The identifiers should be queried from the pattern definition tex labels.
  -- (at least theoretically)
  | Grammar.Expr.mixfix symb args => do
    -- Can't use `interpretApp` here, because (due to a bug?) we can't pass explicit instances to it.
    let args <- args.mapM (interpret' meansE)
    appN (interpret symb) args
  | Grammar.Expr.app _ _ => sorry
    -- We want a dumbed-down application here(no implicits).
    -- Typeclasses should be merely a **notational** construct - which in
    -- CNL has gets handled in *patterns*. This should be only for doing
    -- higher order logic.
  | _ => sorry


def not (e: Expr) : MetaM Expr := appN `Not #[e]

def and (p1: Expr) (p2: Expr) : MetaM Expr := appN `And #[p1, p2]

def andN (ps: Array Expr) : MetaM Expr := do
  ps.foldlM and (<- mkConst `True)

def implies (p1: Expr) (p2: Expr) : MetaM Expr :=
  appN `implies #[p1, p2]

-- For the quantifiers, we assume that we are abstracting free variables that
-- already are in context.
-- `For all green gadgets $x$ we have $p$.`
-- -> `∀x. green(x) → p`
def universalQuant (fvars: Array Expr) (bound : Expr) (claim: Expr) : MetaM Expr := do
  -- `implies` ensures that the input is actually a proposition.
  mkForallFVars fvars (<- implies bound claim)

-- `For some blue gadget $x$ we have $p$.`
-- -> `∃x. blue(x) ∧ p`
def existentialQuant (fvars: Array Expr) (bound : Expr) (claim: Expr) : MetaM Expr := do
  let typeFamily <- mkLambdaFVars fvars <| <- and bound claim
  appN `Exists #[typeFamily]

def nonexistentialQuant (fvars: Array Expr) (bound : Expr) (claim: Expr) : MetaM Expr := do
  appN `not #[<- existentialQuant fvars bound claim]

mutual
  -- Patterns add indirection.
  partial instance meansF : Means Grammar.Fun (MetaM Expr) where
    interpret
    | Grammar.Fun.mk lexicalPhrase args =>
        interpretApp (m2 := meansT) lexicalPhrase args

  partial instance meansT : Means Grammar.Term (MetaM Expr) where
    interpret
    | Grammar.Term.expr e => interpret e
    | Grammar.Term.function f => interpret' meansF f
end


private def mkPred [m1: Means α Name] [m2: Means β (MetaM Expr)] (ident: α) (args: Array β) (e: Expr) : MetaM Expr := do
    let p <- interpretApp ident args
    app p e

-- We encode many of these grammatical constructs as functions `α -> MetaM Expr`, `e ↦ p(x1,...,xn , e)`.
-- This could have been done by using actual functions *inside* lean, but that
-- meant that I had to deal with implicit arguments/polymorphism when applying connectives.
-- Moreover, the outup this setup produces should be much more readable.
instance meansNoun [Means α (MetaM Expr)]: Means (Grammar.Noun α) (Expr -> MetaM Expr) where
  interpret
  | Grammar.Noun.mk sgPl args => mkPred sgPl args

instance meansAdj [Means α (MetaM Expr)]: Means (Grammar.Adj α) (Expr -> MetaM Expr) where
  interpret
  | Grammar.Adj.mk pat args => mkPred pat args

instance meansVerb [Means α (MetaM Expr)]: Means (Grammar.Verb α) (Expr -> MetaM Expr) where
  interpret
  | Grammar.Verb.mk sgPl args => mkPred sgPl args

instance meansVP: Means Grammar.VerbPhrase (Expr -> MetaM Expr) where
  interpret
  | Grammar.VerbPhrase.verb verb => interpret verb
  | Grammar.VerbPhrase.adj adj => interpret adj
  -- For some reason we also need explicit instances here.
  | Grammar.VerbPhrase.verbNot verb => fun e => do
    not (<- interpret' meansVerb verb e)
  | Grammar.VerbPhrase.adjNot adj => fun e => do
    not (<- interpret' meansAdj adj e)

instance meansAdjL: Means Grammar.AdjL (Expr -> MetaM Expr) where
  interpret
  | Grammar.AdjL.mk pat args => mkPred pat args

instance meansAdjR: Means Grammar.AdjR (Expr -> MetaM Expr) where
  interpret
  | Grammar.AdjR.adjR pat args => mkPred pat args
  | Grammar.AdjR.attrRThat verbPhrase => interpret verbPhrase


-- Eventually we want to support optional type annotations in binders (in `vars`)
partial def inContext (vars: Array Name) (k: Array Expr -> MetaM α) : MetaM α :=
  -- This rather messy code shows that higher order functions don't compose
  -- too well.
  let rec loop (i : Nat) (declaredVars : Array Expr) : MetaM α := do
    if h : i < vars.size then
      let name := vars.get ⟨i,h⟩
      let u <- mkFreshLevelMVar
      let type <- mkFreshExprMVar (mkSort u)
      withLocalDecl name BinderInfo.default type fun fvar =>
        loop (i+1) (declaredVars.push fvar)
    else
      k declaredVars
  loop 0 #[]

-- Wohoo, this works!!
-- set_option trace.Meta.debug true
-- def test : MetaM Unit := do
--   let lc <- getLCtx
--   trace[Meta.debug] "before: {lc.getFVarIds}"
--   inContext #[Name.mkSimple "x", Name.mkSimple "y"] fun fvars => do
--     let lc <- getLCtx
--     trace[Meta.debug] "after: {lc.getFVarIds}"
-- #eval test

instance : Means Grammar.Bound (MetaM Expr) where
  interpret
  | Grammar.Bound.unbounded => sorry
  | Grammar.Bound.bounded sgn relator expr => sorry

mutual
  -- Ex: `[Aut(M) is] a simple group $G$ such that the order $G$ is odd.`
  -- Returns a map `Expr -> Expr`, `e ↦ p(e)` for a predicate `p`.
  -- The statement at the end interprets to an expression (not dependent on another expression!)
  -- So we abstract abstract the free variable `G` and also make it into a map
  -- `Expr -> Expr`.
  partial instance meansNP : Means Grammar.NounPhrase (Expr -> MetaM Expr) where
    interpret
    | Grammar.NounPhrase.mk adjL noun varSymb? adjR stmt? => fun e => do
      let base <- andN #[
        <- interpret' meansAdjL adjL e,
        <- interpret' meansNoun noun e,
        <- interpret' meansAdjR adjR e
        ]
      match varSymb?, stmt? with
      | _, none => base
      | none, some stmt => and base (<- interpret' meansStmt stmt)
      | some varSymb, some stmt => do
        let u <- mkFreshLevelMVar
        let varType <- mkFreshExprMVar (mkSort u)

        let stmtLambda <- withLocalDecl (interpret varSymb) BinderInfo.default varType fun fvar => do
          let stmt <- interpret' meansStmt stmt
          mkLambdaFVars #[fvar] stmt

        and base (<- app stmtLambda e)

  -- This is a proposition that needs to be interpreted with the variable
  -- symbols already in context. See example for `Stmt.quantPhrase`.

  -- Warning: This behaves very differently from `NounPhrase`
  partial instance meansNPV : Means Grammar.NounPhraseVars (MetaM Expr) where
    interpret
    | Grammar.NounPhraseVars.mk adjL noun varSymbs adjR stmt? => do
      let fvars := varSymbs.map interpret |>.map mkFVar
      -- Apply the grammatical predictes to free variables
      let nounProps <- fvars.mapM (interpret noun)
      let adjLProps <- fvars.mapM (interpret adjL)
      let adjRProps <- fvars.mapM (interpret adjR)

      let nounProp <- andN nounProps
      let adjLProp <- andN adjLProps
      let adjRProp <- andN adjRProps

      match stmt? with
      | some stmt => do
        let stmt <- interpret' meansStmt stmt
        andN #[nounProp, adjLProp, adjRProp, stmt]
      | noun => andN #[nounProp, adjLProp, adjRProp]


  partial instance meansStmt : Means Grammar.Stmt (MetaM Expr) where
    interpret
    -- Ex: `[Aut(M) is] a simple group $G$ such that the order $G$ is odd.`
    | Grammar.Stmt.noun term np => do
      let term <- interpret term
      interpret' meansNP np term
    -- Ex: `For all/some/no points $a,b$ we have $p(a,b)$.`
    | Grammar.Stmt.quantPhrase (Grammar.QuantPhrase.mk quantifier np) stmt => do
        let varSymbs := np.vars.map interpret

        inContext varSymbs fun fvars => do
          let np <- interpret' meansNPV np
          let stmt <- interpret' meansStmt stmt
          -- We don't check that these are propositions since the quantification functions already implicitly check that.

          match quantifier with
          | Grammar.Quantifier.universally => universalQuant fvars np stmt
          | Grammar.Quantifier.existentially => existentialQuant fvars np stmt
          | Grammar.Quantifier.nonexistentially => nonexistentialQuant fvars np stmt
    | Grammar.Stmt.symbolicQuantified (Grammar.QuantPhrase.mk quantifier np) varSymbs bound suchThat? claim => sorry
    | _ => sorry
end


-- def interpretAsm (asm : Grammar.Asm) : MetaM Int := sorry
-- -- 1) Simply add the variable to the local context (without type) (say, `x : ?m`).
-- -- 2) Run `MetaM` in that context in order to parse the statement/expression/...

-- -- This should yield an environment of declarations.
-- def interpretPara (p: Grammar.Para) : MetaM Unit := sorry
