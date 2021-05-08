
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

-- This is the main typeclass we structure our interpretation code around
-- After writing quite a lot of code with it I realize that this way of
-- structuring code in lean is quite cumbersome, since we can't use it for things
-- like recursive definitions and currying - so we end up explicitly passing
-- instance implementations half of the time. We would probably be better off without this typeclass.
class Means (α: Type) (β: Type) [Inhabited β] where
  interpret : α -> β

open Means

-- The following two definitions are used in order to write partial
-- instances of `Means`, since currently instances and `partial`
-- don't get along.
instance [Inhabited β]: Inhabited (Means α β) where
  default := mk fun x => arbitrary

def interpret' [Inhabited β] (means : Means α β) := @interpret α β _ means


instance : Means Grammar.Pattern (MetaM Name) where
  interpret pat :=
    pat.foldl (fun acc next => acc ++ toString next) ""
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

instance : Means Grammar.SgPl (MetaM Name) where
  interpret pat := interpret pat.sg

instance : Means Grammar.Relator (MetaM Name) where
  interpret rel := toString rel ++ "Rel"
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

instance : Means Grammar.SymbolicPredicate (MetaM Name) where
  interpret
  | Grammar.SymbolicPredicate.mk s _ =>  toString s ++ "Pred"
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

instance : Means Grammar.VarSymbol Name where
  interpret (var: Grammar.VarSymbol) : Name := match var with
  | Grammar.VarSymbol.namedVar name => Name.mkSimple name
  | _ => `thisShouldNotHappen -- I think this rarely occurs


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


private def interpretApp [m1: Means α (MetaM Name)] [m2: Means β (MetaM Expr)] (ident: α) (args: Array β) : MetaM Expr := do
  appN (<- interpret ident) (<- args.mapM interpret)


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
    appN (<- interpret symb) args
  | Grammar.Expr.app _ _ => throwError "app not implemented yet"
    -- We want a dumbed-down application here(no implicits).
    -- Typeclasses should be merely a **notational** construct - which in
    -- CNL has gets handled in *patterns*. This should be only for doing
    -- higher order logic.
  | _ => throwError "const not implemented yet"

def true: Expr := mkConst `True

def not (e: Expr) : MetaM Expr := appN `Not #[e]

def and (p1: Expr) (p2: Expr) : MetaM Expr := appN `And #[p1, p2]

def or (p1: Expr) (p2: Expr) : MetaM Expr := appN `Or #[p1, p2]

def andN (ps: Array Expr) : MetaM Expr := do
  ps.foldlM and (<- true)

def implies (p1: Expr) (p2: Expr) : MetaM Expr :=
  appN `implies #[p1, p2]

def iff (p1: Expr) (p2: Expr) : MetaM Expr :=
  appN `Iff #[p1, p2]

def xor (p1: Expr) (p2: Expr) : MetaM Expr := do
  -- `resolveGlobalConstNoOverload` expands the name according to current
  -- open declarations.
  appN (<- resolveGlobalConstNoOverload `xor) #[p1, p2]

def nor (p1: Expr) (p2: Expr) : MetaM Expr := do
  appN (<- resolveGlobalConstNoOverload `nor) #[p1, p2]

instance meansSgn: Means Grammar.Sign (Expr -> MetaM Expr) where
  interpret
  | Grammar.Sign.positive => pure
  | Grammar.Sign.negative => not

private def interpretRel (lhs: Array Grammar.Expr) (sgn : Grammar.Sign) (rel: Grammar.Relator) (rhs: Array Grammar.Expr): MetaM Expr := do
    let relator <- interpret rel
    let lhs <- lhs.mapM interpret
    let rhs <- rhs.mapM interpret

    let mut acc := true
    for l in lhs do
      for r in rhs do
        let head <- appN relator #[l, r]
        let acc <- and head acc

    interpret' meansSgn sgn acc

partial instance meansC : Means Grammar.Chain (MetaM Expr) where
  interpret
  | Grammar.Chain.chainBase lhs sgn rel rhs =>
    interpretRel lhs sgn rel rhs
  | Grammar.Chain.chainCons lhs sgn rel tail => do
    let head <- match tail with
    | Grammar.Chain.chainBase rhs _ _ _ =>
      interpretRel lhs sgn rel rhs
    | Grammar.Chain.chainCons rhs _ _ _ =>
      interpretRel lhs sgn rel rhs
    let tail <- interpret' meansC tail

    and head tail

instance : Means Grammar.Formula (MetaM Expr) where
  interpret
  | Grammar.Formula.chain chain => interpret chain
  | Grammar.Formula.predicate p args => do appN (<- interpret p) (<- args.mapM interpret)

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


private def mkPred [m1: Means α (MetaM Name)] [m2: Means β (MetaM Expr)] (ident: α) (args: Array β) (e: Expr) : MetaM Expr := do
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
def inContext (vars: Array Name) (k: Array Expr -> MetaM α) : MetaM α :=
  let inCtx := vars.foldr (fun name k declaredFvars => do
    -- We declare the variable `name` and then run `k` in a context containing
    -- this new free variable.
    let u <- mkFreshLevelMVar
    let type <- mkFreshExprMVar (mkSort u)
    withLocalDecl name BinderInfo.default type fun fvar =>
      k (declaredFvars.push fvar)) k

  -- For some reason we can't directly curry this.
  inCtx #[]


instance meansCon: Means Grammar.Connective (Expr -> Expr -> MetaM Expr) where
  interpret
  | Grammar.Connective.conjunction => and
  | Grammar.Connective.disjunction => or
  | Grammar.Connective.implication => implies
  | Grammar.Connective.equivalence => iff
  | Grammar.Connective.exclusiveOr => xor
  | Grammar.Connective.negatedDisjunction => nor


def mkExistsFVars (fvars: Array Expr) (e: Expr) : MetaM Expr :=
  fvars.foldrM (fun fvar acc => do
    let typeFamily <- mkLambdaFVars #[fvar] acc
    -- We use `mkAppM` since we need to instantiate an implicit argument.
    mkAppM `Exists #[typeFamily]) e

-- Wohoo, this works!!
-- set_option trace.Meta.debug true
-- def test : MetaM Unit := do
--   let lc <- getLCtx
--   trace[Meta.debug] "before: {lc.getFVarIds}"
--   inContext #[`x, `y] fun fvars => do
--     let lc <- getLCtx
--     trace[Meta.debug] "after: {lc.getFVarIds}"

--     let f <- appN `And #[fvars[0], fvars[1]]
--     let e <- mkExistsFVars fvars f
--     trace[Meta.debug] "Result: {e}"
-- #eval test

instance meansQuant: Means Grammar.Quantifier (Array Expr -> Expr -> Expr -> MetaM Expr) where
  interpret
  -- For the quantifiers, we assume that we are abstracting free variables that
  -- already are in context.
  -- `For all green gadgets $x$ we have $p$.`
  -- -> `∀x. green(x) → p`
  | Grammar.Quantifier.universally => fun fvars bound claim => do
  -- `implies` ensures that the input is actually a proposition.
    mkForallFVars fvars (<- implies bound claim)

  -- `For some blue gadget $x$ we have $p$.`
  -- -> `∃x. blue(x) ∧ p`
  | Grammar.Quantifier.existentially => fun fvars bound claim => do
    mkExistsFVars fvars (<- and bound claim)

  | Grammar.Quantifier.nonexistentially => fun fvars bound claim => do
    let exists' <- mkExistsFVars fvars (<- and bound claim)
    not exists'


instance meansBound: Means Grammar.Bound (Expr -> MetaM Expr) where
  interpret
  | Grammar.Bound.unbounded => fun e => true
  | Grammar.Bound.bounded sgn relator expr => fun e => do
    let bound <- appN (<- interpret relator) #[e, <- interpret expr]
    interpret' meansSgn sgn bound

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
      -- Apply the grammatical predictes to all of the free variables
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
    | Grammar.Stmt.formula f => interpret f
    | Grammar.Stmt.verbPhrase term vp => do
      let term <- interpret term
      meansVP.interpret vp term

    -- Ex: `[Aut(M) is] a simple group $G$ such that the order $G$ is odd.`
    | Grammar.Stmt.noun term np => do
      let term <- interpret term
      meansNP.interpret np term
    | Grammar.Stmt.neg stmt => do not (<- interpret' meansStmt stmt)
    | Grammar.Stmt.exists' np => do
        let varSymbs := np.vars.map interpret
        inContext varSymbs fun fvars => do
          mkExistsFVars fvars (<- meansNPV.interpret np)

    | Grammar.Stmt.connected connective stmt1 stmt2 => do
      let stmt1 <- interpret' meansStmt stmt1
      let stmt2 <- interpret' meansStmt stmt2
      meansCon.interpret connective stmt1 stmt2

    -- Ex: `For all/some/no points $a,b$ we have $p(a,b)$.`
    | Grammar.Stmt.quantPhrase (Grammar.QuantPhrase.mk quantifier np) stmt => do
        let varSymbs := np.vars.map interpret

        inContext varSymbs fun fvars => do
          let np <- meansNPV.interpret np
          let stmt <- interpret' meansStmt stmt
          -- We don't check that these are propositions since the quantification functions already implicitly check that.

          meansQuant.interpret quantifier fvars np stmt

    -- Ex: `for all $d ∈ S$ such that $d \divides m, n$, we have that $d = 1$.`
    | Grammar.Stmt.symbolicQuantified quantifier varSymbs bound suchThat? claim => do
      let varSymbs := varSymbs.map interpret

      inContext varSymbs fun fvars => do
        let bounds <- fvars.mapM (meansBound.interpret bound)
        let suchThat <- match suchThat? with
          | some stmt => interpret' meansStmt stmt
          | none => true

        let condition <- and (<- andN bounds) suchThat
        let claim <- interpret' meansStmt claim
        meansQuant.interpret quantifier fvars condition claim
end

-- Run `MetaM Expr` with a given assumption.
-- Ex: `Let $n,m$ be natural numbers. Let $n >= m$. The difference of $n$ and $m$ is $n - m$.`
-- This should interpret to a term
-- `λ n, m, p . minus(n,m)`
-- of type
-- `(n:Nat) -> (m:Nat) -> (n >= m) -> Nat`
-- This will probably take quite a bit of tweaking

-- Properties as type classes? This may give an automated way of handling properties silently, without having to pack and unpack structs or tuples all the time.
def withAssumption (asm: Grammar.Asm) (e: Array Expr -> MetaM Expr) (fvars: Array Expr): MetaM Expr := match asm with
  | Grammar.Asm.suppose stmt => do
    -- This should be a (dependent) lambda abstraction in general
    let (condition : Expr) <- interpret stmt
    withLocalDecl (<- mkFreshId) (BinderInfo.default) condition fun fvar =>
      e (fvars.push fvar)

  | Grammar.Asm.letNoun varSymbs np => do
    let varSymbs := varSymbs.map interpret
    inContext varSymbs fun newVars => do
      let pred := interpret np
      let conditions <- andN (<- newVars.mapM pred)
      withLocalDecl (<- mkFreshId) (BinderInfo.default) conditions fun fvar =>
        e (fvars.append newVars |>.push fvar)
      -- Finally we need to (dependently) lambda abstract the free variables and proofs of the predicates and run `e` in that ctx.
  -- | Grammar.Asm.letIn varSymbs type => do
  --   -- let type <- interpret type
  --   sorry
  | _ => throwError "asm not implemented yet"

-- Hm, not sure whether I should `mkForallFVars` all at once
-- in the end or do it at every `withAssumption` step.
-- Note: For definitions it is really easy to do envision an implementation of implicit arguments(since we specify the ones that should be explicit in the pattern), but for lemmas it is harder.
instance: Means Grammar.Lemma (MetaM Expr) where
  interpret
  | Grammar.Lemma.mk asms stmt =>
    let f := asms.foldr withAssumption (fun fvars => do
      let stmt <- interpret stmt
      mkForallFVars fvars stmt)
    f #[]

-- This should yield an environment of declarations.
-- def interpretPara (p: Grammar.Para) : MetaM Unit := sorry
