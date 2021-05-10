
import CNL4Lean.Grammar
import Lean


namespace CNL4Lean
-- This is a painfully boring deserialization module.
-- This code could be heavily simplified with macros.

open Lean.Json
open Grammar


-- I may not need this..
def toExcept {α: Type u} {ε: Type v} (opt: Option α) (err: ε) : Except ε α := match opt with
  | some x => x
  | none => Except.error err

inductive DeserializationError where
  | unexpectedValue : String -> Lean.Json -> DeserializationError
  | unsupportedFeature : String -> DeserializationError
  | parsingError : String -> DeserializationError

abbrev DeserializeM := ExceptT DeserializationError IO

open DeserializationError

instance : Inhabited DeserializationError where
  default := unexpectedValue "" null

instance : ToString DeserializationError where
  toString
    | unexpectedValue expected json => s!"Expected a json value of type '{expected}', got '{json.compress}'."
    | unsupportedFeature feature => s!"The lean backend does not support {feature}"
    | parsingError msg => s!"Pasing error: {msg}"

def throwUnexpected {α: Type u} {m: Type u -> Type v} [MonadExcept DeserializationError m] (s: String) (json: Lean.Json) : m α :=
  throw (unexpectedValue s json)

-- I originally used the `MonadExcept` class for error handling,
-- but typeclass inference took very long.

-- We also use a non-typeclass type for deserialization in order
-- to make the code check faster and avoid issues with recursion
-- and typeclasses. Moreover there is not much of a benefit to
-- typeclasses if they are only used in this one file.
abbrev Deserialize α := Lean.Json -> DeserializeM α

-- In order to implement `partial`, lean needs to prove that the partial
-- functions we are constructing actually have a total implementation.
-- We provide this implementation implicitly by providing `Inhabited`.
instance : Inhabited (DeserializeM α) where
  default := throw arbitrary


-- def getArr (get : Deserialize α) : Deserialize (Array α)
--   | arr a => a.mapM get
--   | json => throwUnexpected "array" json


def get? (get : Deserialize α) : Deserialize (Option α)
  | Lean.Json.null => none
  | json => some <$> get json

-- We provide this instance in order to temporarily use do notation for
-- `Option`.
private instance : Monad Option where
  pure := some
  bind opt f := match opt with
    | none => none
    | some t => f t

/-- Gets an inductive type constructor name and its arguments in Lean.Json format.
For zero arguments, we return `Lean.Json.null`
For one argument we return the json value of the argument,
and for multiple arguments, we return a json array of json values -/
def getInductive? (json : Lean.Json) : Option (String × Lean.Json) := match json with
  | str s => some (s, Lean.Json.null)
  | json => getInductiveArgs? json
where
  getInductiveArgs? (json : Lean.Json) : Option (String × Lean.Json) := do
    let tag <- json.getObjVal? "tag"
    let tag <- tag.getStr?
    let contents <- json.getObjVal? "contents"
    (tag, contents)


def Delim.get : Deserialize Delim
  | "Invis" => Invis
  | "Paren" => Paren
  | "Brace" => Brace
  | "Bracket" => Bracket
  | json => throwUnexpected "delimiter" json


def Tok.get : Deserialize Tok := fun json =>
  match getInductive? json with
    | some ("Word", str t) => Tok.word t
    | some ("Variable", str t) => Tok.variable' t
    | some ("Symbol", str t) => Tok.symbol t
    | some ("Integer", (n: Int)) => Tok.integer n
    | some ("Command", str t) => Tok.command t
    | some ("Open", t) => Tok.open' <$> Delim.get t
    | some ("Close", t) => Tok.close <$> Delim.get t
    | _ => throwUnexpected "token" json


def VarSymbol.get : Deserialize VarSymbol := fun json =>
  match getInductive? json with
    | some ("NamedVar", str t) => VarSymbol.namedVar t
    | some ("FreshVar", (n: Int)) => VarSymbol.freshVar n
    | _ => throwUnexpected "variable symbol" json

def Pattern.get : Deserialize Pattern
  | arr a => a.mapM (get? Tok.get)
  | json => throwUnexpected "pattern" json


partial def Expr.get (json: Lean.Json) : DeserializeM Expr := match getInductive? json with
  | some ("ExprVar", varSymb) => Expr.var <$> VarSymbol.get varSymb
  | some ("ExprInteger", (n : Int)) => Expr.int n
  | some ("ExprConst", t) => Expr.const <$> Tok.get t
  | some ("ExprMixfix", arr #[pattern, arr args]) => do
    let pattern <- Pattern.get pattern
    let args <- args.mapM get
    Expr.mixfix pattern args
  | _ => throwUnexpected "expression" json

def Sign.get : Deserialize Sign
  | "Positive" => Sign.positive
  | "Negative" => Sign.negative
  | json => throwUnexpected "sign" json


private partial def Chain.get : Deserialize Chain := fun json => match getInductive? json with
  | some ("ChainBase", arr #[arr leftExprs, sgn, rel, arr rightExprs]) => do
    let leftExprs <- leftExprs.mapM Expr.get
    let sgn <- Sign.get sgn
    let rel <- Tok.get rel
    let rightExprs <- rightExprs.mapM Expr.get
    Chain.chainBase leftExprs sgn rel rightExprs
  | some ("ChainCons", arr #[arr leftExprs, sgn, rel, chain]) => do
    let leftExprs <- leftExprs.mapM Expr.get
    let sgn <- Sign.get sgn
    let rel <- Tok.get rel
    let chain <- get chain
    Chain.chainCons leftExprs sgn rel chain
  | _ => throwUnexpected "chain" json


def SymbolicPredicate.get : Deserialize SymbolicPredicate
  | arr #[str pred, (arity : Int)] => SymbolicPredicate.mk pred arity
  | json => throwUnexpected "symbolic predicate" json


def Formula.get : Deserialize Formula := fun json => match getInductive? json with
  | some ("FormulaChain", t) => Formula.chain <$> Chain.get t
  | some ("FormulaPredicate", arr #[pred, arr args]) =>
    Formula.predicate <$> SymbolicPredicate.get pred <*> args.mapM Expr.get
  | _ => throwUnexpected "formula" json

def SgPl.get : Deserialize SgPl := fun json => do
    let sg <- match json.getObjVal? "sg" with
      | some sg => Pattern.get sg
      | none => throwUnexpected "SgPl" json

    let pl <- match json.getObjVal? "pl" with
      | some pl => Pattern.get pl
      | none => throwUnexpected "SgPl" json

    pure { sg := sg, pl := pl }

mutual
  partial def getTerm : Deserialize Term := fun json => match getInductive? json with
    | some ("TermExpr", t) => Term.expr <$> Expr.get t
    | some ("TermFun", t) => Term.function <$> getFun t
    | _ => throwUnexpected "term" json

  partial def getFun : Deserialize Fun
    | arr #[sgPl, arr args] => Fun.mk <$> SgPl.get sgPl <*> args.mapM getTerm'
    | json => throwUnexpected "functional noun" json
  where
    -- This is a workaround for a bug, where the lean kernel doesn't find
    -- the `getdTerm` namespace when passed to `mapM`
    getTerm' := getTerm
end

def Term.get := getTerm
def Fun.get := getFun

def Noun.get (get: Deserialize α) : Deserialize (Noun α)
  | arr #[sgPl, arr args] =>
    Noun.mk <$> SgPl.get sgPl <*> args.mapM get
  | json => throwUnexpected "noun" json

def Adj.get (get: Deserialize α) : Deserialize (Adj α)
  | arr #[pat, arr args] =>
    Adj.mk <$> Pattern.get pat <*> args.mapM get
  | json => throwUnexpected "adjective" json

def Verb.get (get: Deserialize α) : Deserialize (Verb α)
  | arr #[sgPl, arr args] =>
    Verb.mk <$> SgPl.get sgPl <*> args.mapM get
  | json => throwUnexpected "verb" json

def VerbPhrase.get : Deserialize VerbPhrase := fun json => match getInductive? json with
    | some ("VPVerb", t) => VerbPhrase.verb <$> Verb.get Term.get t
    | some ("VPAdj", t) => VerbPhrase.adj <$> Adj.get Term.get t
    | some ("VPVerbNot", t) => VerbPhrase.verbNot <$> Verb.get Term.get t
    | some ("VPAdjNot", t) => VerbPhrase.adjNot <$> Adj.get Term.get t
    | _ => throwUnexpected "verb phrase" json

def AdjL.get : Deserialize AdjL
  | arr #[pat, arr args] =>
    AdjL.mk <$> Pattern.get pat <*> args.mapM Term.get
  | json => throwUnexpected "left adjective" json

def AdjR.get : Deserialize AdjR := fun json => match getInductive? json with
  | some ("AdjR", arr #[pat, arr args]) =>
    AdjR.adjR <$> Pattern.get pat <*> args.mapM Term.get
  | _ => throwUnexpected "right adjective" json

def Connective.get : Deserialize Connective
  | "Conjunction" => Connective.conjunction
  | "Disjunction" => Connective.disjunction
  | "Implication" => Connective.implication
  | "Equivalence" => Connective.equivalence
  | "ExclusiveOr" => Connective.exclusiveOr
  | "NegatedDisjunction" => Connective.negatedDisjunction
  | json => throwUnexpected "connective" json

def Quantifier.get : Deserialize Quantifier
  | "Universally" => Quantifier.universally
  | "Existentially" => Quantifier.existentially
  | "Nonexistentially" => Quantifier.nonexistentially
  | json => throwUnexpected "quantifier" json

def Bound.get : Deserialize Bound := fun json => match getInductive? json with
    | some ("Unbounded", Lean.Json.null) => Bound.unbounded
    | some ("Bounded", arr #[sgn, rel, expr]) => Bound.bounded
        <$> Sign.get sgn
        <*> Tok.get rel
        <*> Expr.get expr
    | _ => throwUnexpected "bound" json

mutual
  private partial def getNP : Lean.Json -> DeserializeM NounPhrase
    | arr #[arr adjL, noun, var?, arr adjR, stmt?] => NounPhrase.mk
        <$> adjL.mapM AdjL.get
        <*> Noun.get Term.get noun
        <*> get? VarSymbol.get var?
        <*> adjR.mapM AdjR.get
        <*> get? getStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def getNPVars : Lean.Json -> DeserializeM NounPhraseVars
    | arr #[arr adjL, noun, arr vars, arr adjR, stmt?] => NounPhraseVars.mk
        <$> adjL.mapM AdjL.get
        <*> Noun.get Term.get noun
        <*> vars.mapM VarSymbol.get
        <*> adjR.mapM AdjR.get
        <*> get? getStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def getQPhrase : Lean.Json -> DeserializeM QuantPhrase
    | arr #[quant, np] => QuantPhrase.mk <$> Quantifier.get quant <*> getNPVars np
    | json => throwUnexpected "quantified phrase" json

  private partial def getStmt (json: Lean.Json) : DeserializeM Stmt := match getInductive? json with
    | some ("StmtFormula", t) => Stmt.formula <$> Formula.get t
    | some ("StmtVerbPhrase", arr #[term, verbPhrase]) => Stmt.verbPhrase
        <$> Term.get term
        <*> VerbPhrase.get verbPhrase
    | some ("StmtNoun", arr #[term, np]) => Stmt.noun
        <$> Term.get term
        <*> getNP np
    | some ("StmtNeg", t) => Stmt.neg <$> getStmt t
    | some ("StmtExists", t) => Stmt.exists' <$> getNPVars t
    | some ("StmtConnected", arr #[con, stmt, stmt']) => Stmt.connected
        <$> Connective.get con
        <*> getStmt stmt
        <*> getStmt stmt'
    | some ("StmtQuantPhrase", arr #[qPhrase, stmt]) => Stmt.quantPhrase
        <$> getQPhrase qPhrase
        <*> getStmt stmt
    | some ("SymbolicQuantified", arr #[quantifier, arr varSymbs, bound, suchThat, stmt]) => Stmt.symbolicQuantified
        <$> Quantifier.get quantifier
        <*> varSymbs.mapM VarSymbol.get
        <*> Bound.get bound
        <*> getStmt suchThat
        <*> getStmt stmt
    | _ => throwUnexpected "statement" json
end

def NounPhrase.get := getNP
def NounPhraseVars.get := getNPVars
def QuantPhrase.get := getQPhrase
def Stmt.get := getStmt

def DefnHead.get : Deserialize DefnHead := fun json => match getInductive? json with
  | some ("DefnAdj", arr #[np, varSymb, adj]) => DefnHead.adj
      <$> get? NounPhrase.get np
      <*> VarSymbol.get varSymb
      <*> Adj.get VarSymbol.get adj
  | some ("DefnVerb", arr #[np, varSymb, verb]) => DefnHead.verb
      <$> get? NounPhrase.get np
      <*> VarSymbol.get varSymb
      <*> Verb.get VarSymbol.get verb
  | some ("DefnNoun", arr #[varSymb, noun]) => DefnHead.noun
      <$> VarSymbol.get varSymb
      <*> Noun.get VarSymbol.get noun
  | some ("DefnRel", arr #[varSymb, rel, varSymb']) => DefnHead.rel
      <$> VarSymbol.get varSymb
      <*> Tok.get rel
      <*> VarSymbol.get varSymb'
  | some ("DefnSymbolicPredicate", arr #[symbPred, arr varSymbs]) => DefnHead.symbolicPredicate
      <$> SymbolicPredicate.get symbPred
      <*> varSymbs.mapM VarSymbol.get
  | _ => throwUnexpected "definition head" json

def Asm.get : Deserialize Asm := fun json => match getInductive? json with
  | some ("AsmSuppose", stmt) => Asm.suppose <$> Stmt.get stmt
  | some ("AsmLetNoun", arr #[arr vs, np]) => Asm.letNoun
      <$> vs.mapM VarSymbol.get
      <*> NounPhrase.get np
  | some ("AsmLetIn", arr #[arr vs, expr]) => Asm.letIn
      <$> vs.mapM VarSymbol.get
      <*> Expr.get expr
  | some ("AsmLetThe", arr #[vs, fNoun]) => Asm.letThe
      <$> VarSymbol.get vs
      <*> Fun.get fNoun
  | some ("AsmLetEq", arr #[vs, expr]) => Asm.letEq
      <$> VarSymbol.get vs
      <*> Expr.get expr
  | _ => throwUnexpected "assumption" json

def Defn.get : Deserialize Defn := fun json => match getInductive? json with
  | some ("Defn", arr #[arr asms, defnHead, stmt]) => Defn.defn
      <$> asms.mapM Asm.get
      <*> DefnHead.get defnHead
      <*> Stmt.get stmt
  | some ("DefnFun", arr #[arr asms, fNoun, term?, term]) => Defn.fun'
      <$> asms.mapM Asm.get
      <*> Fun.get fNoun
      <*> get? Term.get term?
      <*> Term.get term
  | _ => throwUnexpected "definition" json

-- instance : Deserializable Axiom where
--   get json := match getInductive? json with
--     | some ("Axiom", arr #[asms, stmt]) => Axiom.mk
--         <$> get asms
--         <*> get stmt
--     | _ => throwUnexpected "axiom" json

def Lemma.get : Deserialize Lemma
  | arr #[arr asms, stmt] => Lemma.mk
      <$> asms.mapM Asm.get
      <*> Stmt.get stmt
  | json => throwUnexpected "lemma" json

def Para.get : Deserialize Para := fun json => match getInductive? json with
  | some ("ParaDefn", defn) => Para.defn' <$> Defn.get defn
  | some ("ParaLemma", arr #[tag, lem]) => Para.lemma' #[]
      <$> Lemma.get lem
  | _ => throwUnexpected "paragraph" json
