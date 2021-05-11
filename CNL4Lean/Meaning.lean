
import CNL4Lean.Grammar
import CNL4Lean.Proposition
import Lean
-- The goal is to create a dummy file and to write all the natural constructs to it.
-- Then, can I somehow make the environment into an `.olean` file? I am not sure how
-- this would work.

namespace CNL4Lean

open Lean hiding Expr
open Lean.Meta

-- In this module I use the `MetaM` monad as a logic framework that exposes leans
-- internals. I decided against using the `TermElabM` monad, because it contains many
-- lean-specific mechanisms, like macro expansion and debugging. Most of the instances
-- for `TermElabM` contain lean-specific `Syntax` objects or macro stuff.

open Proposition

def Pattern.interpret (pat : Pattern) : MetaM Name :=
    pat.foldl (fun acc next => acc ++ toString next) ""
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

def SgPl.interpret (pat: SgPl) : MetaM Name := pat.sg.interpret

def Relator.interpret (rel: Relator) : MetaM Name := toString rel ++ "Rel"
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

def SymbolicPredicate.interpret : SymbolicPredicate -> MetaM Name
  | SymbolicPredicate.mk s _ =>  toString s ++ "Pred"
      |> Name.mkSimple
      |> resolveGlobalConstNoOverload

-- This only extracts the name, it does not look it up in the local context
def VarSymbol.interpret (var: VarSymbol) : Name := match var with
  | VarSymbol.namedVar name => Name.mkSimple name
  | _ => `thisShouldNotHappen -- I think this rarely occurs

def VarSymbol.interpretArr (a: Array VarSymbol) : Array Name :=
  a.map (fun x => x.interpret)

-- Simple unifying application.
-- * Doesn't deal with different argument types
-- * No coercions
-- * No propagating expected type for smarter coercions
-- * No synthetic metavariables
-- The lean application implementation is in `Elab/App.lean` and it has
-- **a lot** more features.
private def app (f: Lean.Expr) (arg: Lean.Expr) : MetaM Lean.Expr := do
  let fType <- inferType f
  let dom <- fType.bindingDomain!
  let type <- inferType arg
  unless <- isDefEq dom type do throwError "Expected type {dom}, got {type}"
  mkApp f arg

-- Copied from `AppBuilder.lean`. Instantiates universe parameters.
private def mkFun (constName : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType := cinfo.instantiateTypeLevelParams us
  return (f, fType)

private def appN (ident: Name) (args: Array Lean.Expr) : MetaM Lean.Expr := do
  let f <- mkFun ident
  args.foldlM (fun f arg => app f arg) f.1


partial def Expr.interpret : Expr -> MetaM Lean.Expr
  | var varSymb => do
    -- Inspired by `resolveLocalName` in `Elab/Term.lean`
    let lctx <- getLCtx
    let varSymb := varSymb.interpret
    match lctx.findFromUserName? varSymb with
    | some ldecl => ldecl.toExpr
    | none => throwError "Variable {varSymb} symbol not found in local context."
  | int (Int.ofNat n) => mkNatLit n
  | int _ => panic! "Integer literals can't be negative."
  -- The identifiers should be queried from the pattern definition tex labels.
  -- (at least theoretically)
  | mixfix symb args => do
    -- Can't use `interpretApp` here, because (due to a bug?) we can't pass explicit instances to it.
    let args <- args.mapM (fun e => e.interpret)
    appN (<- symb.interpret) args
  | app _ _ => throwError "app not implemented yet"
    -- We want a dumbed-down application here(no implicits).
    -- Typeclasses should be merely a **notational** construct - which in
    -- CNL has gets handled in *patterns*. This should be only for doing
    -- higher order logic.
  | _ => throwError "const not implemented yet"


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

def Sign.interpret : Sign -> Proposition -> MetaM Proposition
  | positive => pure
  | negative => not

def Chain.interpretStep (lhs: Array Expr) (sgn : Sign) (rel: Relator) (rhs: Array Expr): MetaM Proposition := do
    let relator <- rel.interpret
    let lhs <- lhs.mapM (fun x => x.interpret)
    let rhs <- rhs.mapM (fun x => x.interpret)

    let mut acc := top
    for l in lhs do
      for r in rhs do
        let head <- expr <$> appN relator #[l, r]
        let acc <- and head acc

    sgn.interpret acc

partial def Chain.interpret : Chain -> MetaM Proposition
  | chainBase lhs sgn rel rhs => interpretStep lhs sgn rel rhs
  | chainCons lhs sgn rel tail => do
    let head <- match tail with
    | chainBase rhs _ _ _ => interpretStep lhs sgn rel rhs
    | chainCons rhs _ _ _ => interpretStep lhs sgn rel rhs
    let tail <- tail.interpret

    and head tail

def Formula.interpret : Formula -> MetaM Proposition
  | chain c => c.interpret
  | predicate p args => do
    let args <- args.mapM (fun arg => arg.interpret)
    expr <$> appN (<- p.interpret) args

mutual
  -- Patterns add indirection.
  partial def interpretFun : Fun -> MetaM Lean.Expr
    | Fun.mk lexicalPhrase args => do
        let args <- args.mapM interpretTerm
        appN (<- lexicalPhrase.interpret) args

  partial def interpretTerm : Term -> MetaM Lean.Expr
    | Term.expr e => e.interpret
    | Term.function f => interpretFun f
end

def Fun.interpret := interpretFun
def Term.interpret := interpretTerm
def Term.interpretArr (a: Array Term) : MetaM (Array Lean.Expr) :=
  a.mapM (fun x => x.interpret)

-- TODO: We should have certain predicates that get short-circuited to `top`,
-- for instance if they only exist for the purposes of type inference.
private def mkPred (ident: Name) (args: Array Lean.Expr) (e: Lean.Expr) : MetaM Proposition := do
    let p <- appN ident args
    expr <$> app p e

-- private def mkPredV (ident: Name) (args: Array VarSymbol) (e: Lean.Expr) : MetaM Lean.Expr := do
--     let p <- appN ident (VarSymbol.interpretArr args)
--     app p e

-- We encode many of these grammatical constructs as functions `α -> MetaM Expr`, `e ↦ p(x1,...,xn , e)`.
-- This could have been done by using actual functions *inside* lean, but that
-- meant that I had to deal with implicit arguments/polymorphism when applying connectives.
-- Moreover, the output this setup produces should be much more readable.
def Noun.interpret : Noun Term -> Lean.Expr -> MetaM Proposition
  | mk sgPl args, e => do
    mkPred (<- sgPl.interpret) (<- Term.interpretArr args) e

def Adj.interpret : Adj Term -> Lean.Expr -> MetaM Proposition
  | mk sgPl args, e => do
    mkPred (<- sgPl.interpret) (<- Term.interpretArr args) e

def Verb.interpret : Verb Term -> Lean.Expr -> MetaM Proposition
  | mk sgPl args, e => do
    mkPred (<- sgPl.interpret) (<- Term.interpretArr args) e

def VerbPhrase.interpret : VerbPhrase -> Lean.Expr -> MetaM Proposition
  | verb v, e => v.interpret e
  | VerbPhrase.adj a, e => a.interpret e
  | verbNot v, e => do not (<- v.interpret e)
  | adjNot a, e => do not (<- a.interpret e)

def AdjL.interpret : AdjL -> Lean.Expr -> MetaM Proposition
  | mk pat args, e => do
    mkPred (<- pat.interpret) (<- Term.interpretArr args) e

def AdjR.interpret : AdjR -> Lean.Expr -> MetaM Proposition
  | adjR pat args, e => do
    mkPred (<- pat.interpret) (<- Term.interpretArr args) e
  | attrRThat verbPhrase, e => verbPhrase.interpret e

-- Eventually we want to support optional type annotations in binders (in `vars`)
def inContext [Inhabited α] (vars: Array Name) (k: Array Lean.Expr -> MetaM α) : MetaM α :=
  withLocalDeclsD (vars.map (fun v => (v,fun _ => mkFreshTypeMVar))) k


def Connective.interpret : Connective -> Proposition -> Proposition -> MetaM Proposition
  | Connective.conjunction => and
  | Connective.disjunction => or
  | Connective.implication => implies
  | Connective.equivalence => iff
  | Connective.exclusiveOr => xor
  | Connective.negatedDisjunction => nor


def mkExistsFVars' (fvars: Array Lean.Expr) (e: Lean.Expr) : MetaM Lean.Expr :=
  fvars.foldrM (fun fvar acc => do
    let typeFamily <- mkLambdaFVars #[fvar] acc
    -- We use `mkAppM` since we need to instantiate an implicit argument.
    mkAppM `Exists #[typeFamily]) e

def mkExistsFVars (fvars: Array Lean.Expr) (p: Proposition) : MetaM Proposition := expr <$> Proposition.run (mkExistsFVars' fvars) p

def Quantifier.interpret : Quantifier -> Array Lean.Expr -> Lean.Expr -> Lean.Expr -> MetaM Lean.Expr
  -- For the quantifiers, we assume that we are abstracting free variables that
  -- already are in context.
  -- `For all green gadgets $x$ we have $p$.`
  -- -> `∀x. green(x) → p`
  | Quantifier.universally => fun fvars bound claim => do
  -- `implies` ensures that the input is actually a proposition.
    mkForallFVars fvars (<- implies bound claim)

  -- `For some blue gadget $x$ we have $p$.`
  -- -> `∃x. blue(x) ∧ p`
  | Quantifier.existentially => fun fvars bound claim => do
    mkExistsFVars fvars (<- and bound claim)

  | Quantifier.nonexistentially => fun fvars bound claim => do
    let exists' <- mkExistsFVars fvars (<- and bound claim)
    not exists'


instance meansBound: Means Bound (Expr -> MetaM Expr) where
  interpret
  | Bound.unbounded => fun e => true
  | Bound.bounded sgn relator expr => fun e => do
    let bound <- appN (<- interpret relator) #[e, <- interpret expr]
    interpret' meansSgn sgn bound

mutual
  -- Ex: `[Aut(M) is] a simple group $G$ such that the order $G$ is odd.`
  -- Returns a map `Expr -> Expr`, `e ↦ p(e)` for a predicate `p`.
  -- The statement at the end interprets to an expression (not dependent on another expression!)
  -- So we abstract abstract the free variable `G` and also make it into a map
  -- `Expr -> Expr`.
  partial instance meansNP : Means NounPhrase (Expr -> MetaM Expr) where
    interpret
    | NounPhrase.mk adjL noun varSymb? adjR stmt? => fun e => do
      let adjL <- andN (<- adjL.mapM (fun x => interpret' meansAdjL x e))
      let adjR <- andN (<- adjR.mapM (fun x => interpret' meansAdjR x e))
      let noun <- interpret' meansNoun noun e
      let base <- andN #[adjL, noun, adjR]

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
  partial instance meansNPV : Means NounPhraseVars (MetaM Expr) where
    interpret
    | NounPhraseVars.mk adjL noun varSymbs adjR stmt? => do
      let fvars <- varSymbs.map Expr.var |>.mapM interpret

      -- This should be refactored out since it is also used by `NounPhrase`.
      -- But since we are currently using typeclasses to structure
      -- interpretations it would be a bit akward.
      let adjL (e: Expr) : MetaM Expr := do
        andN (<- adjL.mapM (fun x => interpret' meansAdjL x e))
      let adjR (e: Expr) : MetaM Expr := do
        andN (<- adjR.mapM (fun x => interpret' meansAdjR x e))

      -- Apply the grammatical predictes to all of the free variables
      let nounProps <- fvars.mapM (interpret noun)
      let adjLProps <- fvars.mapM adjL
      let adjRProps <- fvars.mapM adjR

      let nounProp <- andN nounProps
      let adjLProp <- andN adjLProps
      let adjRProp <- andN adjRProps

      match stmt? with
      | some stmt => do
        let stmt <- interpret' meansStmt stmt
        andN #[nounProp, adjLProp, adjRProp, stmt]
      | noun => andN #[nounProp, adjLProp, adjRProp]


  partial instance meansStmt : Means Stmt (MetaM Expr) where
    interpret
    | Stmt.formula f => interpret f
    | Stmt.verbPhrase term vp => do
      let term <- interpret term
      meansVP.interpret vp term

    -- Ex: `[Aut(M) is] a simple group $G$ such that the order $G$ is odd.`
    | Stmt.noun term np => do
      let term <- interpret term
      meansNP.interpret np term
    | Stmt.neg stmt => do not (<- interpret' meansStmt stmt)
    | Stmt.exists' np => do
        let varSymbs := np.vars.map interpret
        inContext varSymbs fun fvars => do
          mkExistsFVars fvars (<- meansNPV.interpret np)

    | Stmt.connected connective stmt1 stmt2 => do
      let stmt1 <- interpret' meansStmt stmt1
      let stmt2 <- interpret' meansStmt stmt2
      meansCon.interpret connective stmt1 stmt2

    -- Ex: `For all/some/no points $a,b$ we have $p(a,b)$.`
    | Stmt.quantPhrase (QuantPhrase.mk quantifier np) stmt => do
        let varSymbs := np.vars.map interpret

        inContext varSymbs fun fvars => do
          let lc <- getLCtx

          -- We don't check that these are propositions since the quantification functions already implicitly check that.
          let np <- meansNPV.interpret np
          let stmt <- interpret' meansStmt stmt

          meansQuant.interpret quantifier fvars np stmt

    -- Ex: `for all $d ∈ S$ such that $d \divides m, n$, we have that $d = 1$.`
    | Stmt.symbolicQuantified quantifier varSymbs bound suchThat? claim => do
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
-- Hm, it seems like automatically resolving arguments like `n >= m`
-- is a problem very similar to subtyping. I should search for `subtype`
-- in the lean source code.

-- Properties as type classes? This may give an automated way of handling properties silently, without having to pack and unpack structs or tuples all the time.
def withAssumption (asm: Asm) (e: Array Expr -> MetaM Expr) (fvars: Array Expr): MetaM Expr := match asm with
  | Asm.suppose stmt => do
    -- This should be a (dependent) lambda abstraction in general
    let (condition : Expr) <- interpret stmt
    withLocalDeclD (<- mkFreshId) condition fun fvar =>
      e (fvars.push fvar)

  | Asm.letNoun varSymbs np => do
    let varSymbs := varSymbs.map interpret
    inContext varSymbs fun newVars => do
      let pred := interpret np
      let conditions <- andN (<- newVars.mapM pred)
      withLocalDeclD (<- mkFreshId) conditions fun fvar =>
        e (fvars.append newVars |>.push fvar)
      -- Finally we need to (dependently) lambda abstract the free variables and proofs of the predicates and run `e` in that ctx.
  -- | Asm.letIn varSymbs type => do
  --   -- let type <- interpret type
  --   sorry
  | _ => throwError "asm not implemented yet"

-- Hm, not sure whether I should `mkForallFVars` all at once
-- in the end or do it at every `withAssumption` step.
-- Note: For definitions it is really easy to do envision an implementation of implicit arguments(since we specify the ones that should be explicit in the pattern), but for lemmas it is harder.
instance: Means Lemma (MetaM Expr) where
  interpret
  | Lemma.mk asms stmt =>
    let f := asms.foldr withAssumption (fun fvars => do
      let stmt <- interpret stmt
      mkForallFVars fvars stmt)
    f #[]

-- This should yield an environment of declarations.
-- def interpretPara (p: Para) : MetaM Unit := sorry
instance: Means Para (MetaM Unit) where
  interpret
  | Para.defn' defn => sorry
    -- Defintions can be auto-named by patterns
  | Para.lemma' tag lemma => do
    let lemma <- interpret lemma
    let type <- inferType lemma

    -- Environment.add sth
    -- Lemmas *cannot* be auto-named
