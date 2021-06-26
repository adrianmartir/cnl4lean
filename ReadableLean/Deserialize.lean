
import Lean
import ReadableLean.Grammar

namespace ReadableLean
-- This is a painfully boring deserialization module.
-- This code could be heavily simplified with macros.

open Lean.Json


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


-- def fromJsonArr (fromJson : Deserialize α) : Deserialize (Array α)
--   | arr a => a.mapM fromJson
--   | json => throwUnexpected "array" json


def fromJson? (fromJson : Deserialize α) : Deserialize (Option α)
  | Lean.Json.null => none
  | json => some <$> fromJson json

-- We provide this instance in order to temporarily use do notation for
-- `Option`.
private instance : Monad Option where
  pure := some
  bind opt f := match opt with
    | none => none
    | some t => f t

/-- fromJsons an inductive type constructor name and its arguments in Lean.Json format.
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
    let contents <- json.getObjValD "contents"
    (tag, contents)


def Delim.fromJson : Deserialize Delim
  | "Invis" => Invis
  | "Paren" => Paren
  | "Brace" => Brace
  | "Bracket" => Bracket
  | json => throwUnexpected "delimiter" json


def Tok.fromJson : Deserialize Tok := fun json =>
  match getInductive? json with
    | some ("Word", str t) => word t
    | some ("Variable", str t) => variable' t
    | some ("Symbol", str t) => symbol t
    | some ("Integer", (n: Int)) => integer n
    | some ("Command", str t) => command t
    | some ("Open", t) => open' <$> Delim.fromJson t
    | some ("Close", t) => close <$> Delim.fromJson t
    | _ => throwUnexpected "token" json


def VarSymbol.fromJson : Deserialize VarSymbol := fun json =>
  match getInductive? json with
    | some ("NamedVar", str t) => namedVar t
    | some ("FreshVar", (n: Int)) => freshVar n
    | _ => throwUnexpected "variable symbol" json

def Pattern.fromJson : Deserialize Pattern
  | arr a => a.mapM (fromJson? Tok.fromJson)
  | json => throwUnexpected "pattern" json


partial def Expr.fromJson (json: Lean.Json) : DeserializeM Expr := match getInductive? json with
  | some ("ExprVar", varSymb) => var <$> VarSymbol.fromJson varSymb
  | some ("ExprInteger", (n : Int)) => Expr.int n
  | some ("ExprConst", t) => const <$> Tok.fromJson t
  | some ("ExprMixfix", arr #[pattern, arr args]) => do
    let pattern <- Pattern.fromJson pattern
    let args <- args.mapM fromJson
    mixfix pattern args
  | _ => throwUnexpected "expression" json

def Sign.fromJson : Deserialize Sign
  | "Positive" => positive
  | "Negative" => negative
  | json => throwUnexpected "sign" json


private partial def Chain.fromJson : Deserialize Chain := fun json => match getInductive? json with
  | some ("ChainBase", arr #[arr leftExprs, sgn, rel, arr rightExprs]) => do
    let leftExprs <- leftExprs.mapM Expr.fromJson
    let sgn <- Sign.fromJson sgn
    let rel <- Tok.fromJson rel
    let rightExprs <- rightExprs.mapM Expr.fromJson
    chainBase leftExprs sgn rel rightExprs
  | some ("ChainCons", arr #[arr leftExprs, sgn, rel, chain]) => do
    let leftExprs <- leftExprs.mapM Expr.fromJson
    let sgn <- Sign.fromJson sgn
    let rel <- Tok.fromJson rel
    let chain <- fromJson chain
    chainCons leftExprs sgn rel chain
  | _ => throwUnexpected "chain" json


def SymbolicPredicate.fromJson : Deserialize SymbolicPredicate
  | arr #[str pred, (arity : Int)] => SymbolicPredicate.mk pred arity
  | json => throwUnexpected "symbolic predicate" json


def Formula.fromJson : Deserialize Formula := fun json => match getInductive? json with
  | some ("FormulaChain", t) => Formula.chain <$> Chain.fromJson t
  | some ("FormulaPredicate", arr #[pred, arr args]) =>
    Formula.predicate <$> SymbolicPredicate.fromJson pred <*> args.mapM Expr.fromJson
  | _ => throwUnexpected "formula" json

def SgPl.fromJson : Deserialize SgPl := fun json => do
    let sg <- match json.getObjVal? "sg" with
      | some sg => Pattern.fromJson sg
      | none => throwUnexpected "SgPl" json

    let pl <- match json.getObjVal? "pl" with
      | some pl => Pattern.fromJson pl
      | none => throwUnexpected "SgPl" json

    pure { sg := sg, pl := pl }

mutual
  partial def fromJsonTerm : Deserialize Term := fun json => match getInductive? json with
    | some ("TermExpr", t) => Term.expr <$> Expr.fromJson t
    | some ("TermFun", t) => Term.function <$> fromJsonFun t
    | _ => throwUnexpected "term" json

  partial def fromJsonFun : Deserialize Fun
    | arr #[sgPl, arr args] => Fun.mk <$> SgPl.fromJson sgPl <*> args.mapM fromJsonTerm'
    | json => throwUnexpected "functional noun" json
  where
    -- This is a workaround for a bug, where the lean kernel doesn't find
    -- the `fromJsondTerm` namespace when passed to `mapM`
    fromJsonTerm' := fromJsonTerm
end

def Term.fromJson := fromJsonTerm
def Fun.fromJson := fromJsonFun

def Noun.fromJson (fromJson: Deserialize α) : Deserialize (Noun α)
  | arr #[sgPl, arr args] =>
    mk <$> SgPl.fromJson sgPl <*> args.mapM fromJson
  | json => throwUnexpected "noun" json

def Adj.fromJson (fromJson: Deserialize α) : Deserialize (Adj α)
  | arr #[pat, arr args] =>
    mk <$> Pattern.fromJson pat <*> args.mapM fromJson
  | json => throwUnexpected "adjective" json

def Verb.fromJson (fromJson: Deserialize α) : Deserialize (Verb α)
  | arr #[sgPl, arr args] =>
    mk <$> SgPl.fromJson sgPl <*> args.mapM fromJson
  | json => throwUnexpected "verb" json

def VerbPhrase.fromJson : Deserialize VerbPhrase := fun json => match getInductive? json with
    | some ("VPVerb", t) => VerbPhrase.verb <$> Verb.fromJson Term.fromJson t
    | some ("VPAdj", t) => VerbPhrase.adj <$> Adj.fromJson Term.fromJson t
    | some ("VPVerbNot", t) => VerbPhrase.verbNot <$> Verb.fromJson Term.fromJson t
    | some ("VPAdjNot", t) => VerbPhrase.adjNot <$> Adj.fromJson Term.fromJson t
    | _ => throwUnexpected "verb phrase" json

def AdjL.fromJson : Deserialize AdjL
  | arr #[pat, arr args] =>
    mk <$> Pattern.fromJson pat <*> args.mapM Term.fromJson
  | json => throwUnexpected "left adjective" json

def AdjR.fromJson : Deserialize AdjR := fun json => match getInductive? json with
  | some ("AdjR", arr #[pat, arr args]) =>
    adjR <$> Pattern.fromJson pat <*> args.mapM Term.fromJson
  | _ => throwUnexpected "right adjective" json

def Connective.fromJson : Deserialize Connective
  | "Conjunction" => conjunction
  | "Disjunction" => disjunction
  | "Implication" => implication
  | "Equivalence" => equivalence
  | "ExclusiveOr" => exclusiveOr
  | "NegatedDisjunction" => negatedDisjunction
  | json => throwUnexpected "connective" json

def Quantifier.fromJson : Deserialize Quantifier
  | "Universally" => universally
  | "Existentially" => existentially
  | "Nonexistentially" => nonexistentially
  | json => throwUnexpected "quantifier" json

def Bound.fromJson : Deserialize Bound := fun json => match getInductive? json with
    | some ("Unbounded", Lean.Json.null) => unbounded
    | some ("Bounded", arr #[sgn, rel, expr]) => bounded
        <$> Sign.fromJson sgn
        <*> Tok.fromJson rel
        <*> Expr.fromJson expr
    | _ => throwUnexpected "bound" json

mutual
  private partial def fromJsonNP : Lean.Json -> DeserializeM NounPhrase
    | arr #[arr adjL, noun, var?, arr adjR, stmt?] => NounPhrase.mk
        <$> adjL.mapM AdjL.fromJson
        <*> Noun.fromJson Term.fromJson noun
        <*> fromJson? VarSymbol.fromJson var?
        <*> adjR.mapM AdjR.fromJson
        <*> fromJson? fromJsonStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def fromJsonNPVars : Lean.Json -> DeserializeM NounPhraseVars
    | arr #[arr adjL, noun, arr vars, arr adjR, stmt?] => NounPhraseVars.mk
        <$> adjL.mapM AdjL.fromJson
        <*> Noun.fromJson Term.fromJson noun
        <*> vars.mapM VarSymbol.fromJson
        <*> adjR.mapM AdjR.fromJson
        <*> fromJson? fromJsonStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def fromJsonQPhrase : Lean.Json -> DeserializeM QuantPhrase
    | arr #[quant, np] => QuantPhrase.mk <$> Quantifier.fromJson quant <*> fromJsonNPVars np
    | json => throwUnexpected "quantified phrase" json

  private partial def fromJsonStmt (json: Lean.Json) : DeserializeM Stmt := match getInductive? json with
    | some ("StmtFormula", t) => Stmt.formula <$> Formula.fromJson t
    | some ("StmtVerbPhrase", arr #[term, verbPhrase]) => Stmt.verbPhrase
        <$> Term.fromJson term
        <*> VerbPhrase.fromJson verbPhrase
    | some ("StmtNoun", arr #[term, np]) => Stmt.noun
        <$> Term.fromJson term
        <*> fromJsonNP np
    | some ("StmtNeg", t) => Stmt.neg <$> fromJsonStmt t
    | some ("StmtExists", t) => Stmt.exists' <$> fromJsonNPVars t
    | some ("StmtConnected", arr #[con, stmt, stmt']) => Stmt.connected
        <$> Connective.fromJson con
        <*> fromJsonStmt stmt
        <*> fromJsonStmt stmt'
    | some ("StmtQuantPhrase", arr #[qPhrase, stmt]) => Stmt.quantPhrase
        <$> fromJsonQPhrase qPhrase
        <*> fromJsonStmt stmt
    | some ("SymbolicQuantified", arr #[quantifier, arr varSymbs, bound, suchThat, stmt]) => Stmt.symbolicQuantified
        <$> Quantifier.fromJson quantifier
        <*> varSymbs.mapM VarSymbol.fromJson
        <*> Bound.fromJson bound
        <*> fromJson? fromJsonStmt suchThat
        <*> fromJsonStmt stmt
    | _ => throwUnexpected "statement" json
end

def NounPhrase.fromJson := fromJsonNP
def NounPhraseVars.fromJson := fromJsonNPVars
def QuantPhrase.fromJson := fromJsonQPhrase
def Stmt.fromJson := fromJsonStmt

def DefnHead.fromJson : Deserialize DefnHead := fun json => match getInductive? json with
  | some ("DefnAdj", arr #[np, varSymb, a]) => adj
      <$> fromJson? NounPhrase.fromJson np
      <*> VarSymbol.fromJson varSymb
      <*> Adj.fromJson VarSymbol.fromJson a
  | some ("DefnVerb", arr #[np, varSymb, v]) => verb
      <$> fromJson? NounPhrase.fromJson np
      <*> VarSymbol.fromJson varSymb
      <*> Verb.fromJson VarSymbol.fromJson v
  | some ("DefnNoun", arr #[varSymb, n]) => noun
      <$> VarSymbol.fromJson varSymb
      <*> Noun.fromJson VarSymbol.fromJson n
  | some ("DefnRel", arr #[varSymb, r, varSymb']) => rel
      <$> VarSymbol.fromJson varSymb
      <*> Tok.fromJson r
      <*> VarSymbol.fromJson varSymb'
  | some ("DefnSymbolicPredicate", arr #[symbPred, arr varSymbs]) => DefnHead.symbolicPredicate
      <$> SymbolicPredicate.fromJson symbPred
      <*> varSymbs.mapM VarSymbol.fromJson
  | _ => throwUnexpected "definition head" json

def Asm.fromJson : Deserialize Asm := fun json => match getInductive? json with
  | some ("AsmSuppose", stmt) => Asm.suppose <$> Stmt.fromJson stmt
  | some ("AsmLetNoun", arr #[arr vs, np]) => Asm.letNoun
      <$> vs.mapM VarSymbol.fromJson
      <*> NounPhrase.fromJson np
  | some ("AsmLetIn", arr #[arr vs, expr]) => Asm.letIn
      <$> vs.mapM VarSymbol.fromJson
      <*> Expr.fromJson expr
  | some ("AsmLetThe", arr #[vs, fNoun]) => Asm.letThe
      <$> VarSymbol.fromJson vs
      <*> Fun.fromJson fNoun
  | some ("AsmLetEq", arr #[vs, expr]) => Asm.letEq
      <$> VarSymbol.fromJson vs
      <*> Expr.fromJson expr
  | _ => throwUnexpected "assumption" json

def Defn.fromJson : Deserialize Defn := fun json => match getInductive? json with
  | some ("Defn", arr #[arr asms, defnHead, stmt]) => Defn.defn
      <$> asms.mapM Asm.fromJson
      <*> DefnHead.fromJson defnHead
      <*> Stmt.fromJson stmt
  | some ("DefnFun", arr #[arr asms, fNoun, term?, term]) => Defn.fun'
      <$> asms.mapM Asm.fromJson
      <*> Fun.fromJson fNoun
      <*> fromJson? Term.fromJson term?
      <*> Term.fromJson term
  | _ => throwUnexpected "definition" json

-- instance : Deserializable Axiom where
--   fromJson json := match getInductive? json with
--     | some ("Axiom", arr #[asms, stmt]) => Axiom.mk
--         <$> fromJson asms
--         <*> fromJson stmt
--     | _ => throwUnexpected "axiom" json

def Lemma.fromJson : Deserialize Lemma
  | arr #[arr asms, stmt] => Lemma.mk
      <$> asms.mapM Asm.fromJson
      <*> Stmt.fromJson stmt
  | json => throwUnexpected "lemma" json

def Para.fromJson : Deserialize Para := fun json => match getInductive? json with
  | some ("ParaDefn", defn) => Para.defn' <$> Defn.fromJson defn
  | some ("ParaLemma", arr #[null, lem]) => Para.lemma' #[]
      <$> Lemma.fromJson lem
  | some ("ParaLemma", arr #[arr a, lem]) => do
    Para.lemma' (<- a.mapM Tok.fromJson) (<- Lemma.fromJson lem)
  | _ => throwUnexpected "paragraph" json
