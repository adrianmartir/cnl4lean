
import CNL4Lean.Grammar
import Lean


namespace CNL4Lean
-- This is a painfully boring deserialization module.

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

-- I originally used this typeclass for this module:
-- variable [Monad m] [MonadExcept DeserializationError m]
-- But then this module needs like 10 minutes to compile.
-- This is so odd.

class Deserializable (α: Type) where
  deserialize : Lean.Json -> DeserializeM α

open Deserializable

-- In order to implement `partial`, lean needs to prove that the partial
-- functions we are constructing actually have a total implementation.
-- We provide this implementation implicitly by providing `Inhabited`.
instance : Inhabited (DeserializeM α) where
  default := throw arbitrary


instance [Deserializable α] : Deserializable (Array α) where
  deserialize
    | arr a => a.mapM deserialize
    | json => throwUnexpected "array" json


instance [Deserializable α] : Deserializable (Option α) where
  deserialize
    | Lean.Json.null => none
    | json => some <$> deserialize json

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


instance : Deserializable Delim where
  deserialize
    | "Invis" => Invis
    | "Paren" => Paren
    | "Brace" => Brace
    | "Bracket" => Bracket
    | json => throwUnexpected "delimiter" json


instance : Deserializable Tok where
  deserialize json := match getInductive? json with
    | some ("Word", str t) => Tok.word t
    | some ("Variable", str t) => Tok.variable' t
    | some ("Symbol", str t) => Tok.symbol t
    | some ("Integer", (n: Int)) => Tok.integer n
    | some ("Command", str t) => Tok.command t
    | some ("Open", t) => Tok.open' <$> deserialize t
    | some ("Close", t) => Tok.close <$> deserialize t
    | _ => throwUnexpected "token" json


instance : Deserializable VarSymbol where
  deserialize json := match getInductive? json with
    | some ("NamedVar", str t) => VarSymbol.namedVar t
    | some ("FreshVar", (n: Int)) => VarSymbol.freshVar n
    | _ => throwUnexpected "variable symbol" json


private partial def deserializeExpr (json: Lean.Json) : DeserializeM Expr := match getInductive? json with
    | some ("ExprVar", varSymb) => Expr.var <$> deserialize varSymb
    | some ("ExprInteger", (n : Int)) => Expr.int n
    | some ("ExprConst", t) => Expr.const <$> deserialize t
    | some ("ExprMixfix", arr #[pattern, arr args]) => do
      let pattern <- deserialize pattern
      let args <- args.mapM deserializeExpr
      Expr.mixfix pattern args
    | _ => throwUnexpected "expression" json

instance : Deserializable Expr := mk deserializeExpr

instance : Deserializable Sign where
  deserialize
    | "Positive" => Sign.positive
    | "Negative" => Sign.negative
    | json => throwUnexpected "sign" json


private partial def deserializeChain (json: Lean.Json) : DeserializeM Chain := match getInductive? json with
  | some ("ChainBase", arr #[arr leftExprs, sgn, rel, arr rightExprs]) => do
    let leftExprs <- leftExprs.mapM deserialize
    let sgn <- deserialize sgn
    let rel <- deserialize rel
    let rightExprs <- rightExprs.mapM deserialize
    Chain.chainBase leftExprs sgn rel rightExprs
  | some ("ChainCons", arr #[arr leftExprs, sgn, rel, chain]) => do
    let leftExprs <- leftExprs.mapM deserialize
    let sgn <- deserialize sgn
    let rel <- deserialize rel
    let chain <- deserializeChain chain
    Chain.chainCons leftExprs sgn rel chain
  | _ => throwUnexpected "chain" json


instance : Deserializable Chain where
  deserialize := deserializeChain

instance : Deserializable SymbolicPredicate where
  deserialize
    | arr #[str pred, (arity : Int)] => SymbolicPredicate.mk pred arity
    | json => throwUnexpected "symbolic predicate" json


instance : Deserializable Formula where
  deserialize (json: Lean.Json) : DeserializeM Formula := match getInductive? json with
  | some ("FormulaChain", t) => Formula.chain <$> deserialize t
  | some ("FormulaPredicate", arr #[pred, arr args]) =>
    Formula.predicate <$> deserialize pred <*> args.mapM deserialize
  | _ => throwUnexpected "formula" json

instance : Deserializable SgPl where
  deserialize (json: Lean.Json) : DeserializeM SgPl := do
    let sg <- match json.getObjVal? "sg" with
      | some sg => deserialize sg
      | none => throwUnexpected "SgPl" json

    let pl <- match json.getObjVal? "pl" with
      | some pl => deserialize pl
      | none => throwUnexpected "SgPl" json

    pure { sg := sg, pl := pl }

mutual
  partial def deserializeTerm (json: Lean.Json): DeserializeM Term := match getInductive? json with
    | some ("TermExpr", t) => Term.expr <$> deserialize t
    | some ("TermFun", t) => Term.function <$> deserializeFun t
    | _ => throwUnexpected "term" json

  partial def deserializeFun : Lean.Json -> DeserializeM Fun
    | arr #[sgPl, arr args] => Fun.mk <$> deserialize sgPl <*> args.mapM deserializeTerm'
    | json => throwUnexpected "functional noun" json
  where
    -- This is a workaround for a bug, where the lean kernel doesn't find
    -- the `deserializedTerm` namespace when passed to `mapM`
    deserializeTerm' := deserializeTerm
end


instance : Deserializable Fun := mk deserializeFun
instance : Deserializable Term := mk deserializeTerm

instance [Deserializable α]: Deserializable (Noun α) where
  deserialize
    | arr #[sgPl, arr args] =>
      Noun.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "noun" json

instance [Deserializable α]: Deserializable (Adj α) where
  deserialize
    | arr #[sgPl, arr args] =>
      Adj.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "adjective" json

instance [Deserializable α]: Deserializable (Verb α) where
  deserialize
    | arr #[sgPl, arr args] =>
      Verb.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "verb" json

instance : Deserializable VerbPhrase where
  deserialize (json: Lean.Json) : DeserializeM VerbPhrase := match getInductive? json with
    | some ("VPVerb", t) => VerbPhrase.verb <$> deserialize t
    | some ("VPAdj", t) => VerbPhrase.adj <$> deserialize t
    | some ("VPVerbNot", t) => VerbPhrase.verbNot <$> deserialize t
    | some ("VPAdjNot", t) => VerbPhrase.adjNot <$> deserialize t
    | _ => throwUnexpected "verb phrase" json

instance : Deserializable AdjL where
  deserialize
    | arr #[sgPl, arr args] =>
      AdjL.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "left adjective" json

instance : Deserializable AdjR where
  deserialize (json: Lean.Json) : DeserializeM AdjR := match getInductive? json with
    | some ("AdjR", arr #[sgPl, arr args]) =>
      AdjR.adjR <$> deserialize sgPl <*> args.mapM deserialize
    | _ => throwUnexpected "right adjective" json

instance : Deserializable Connective where
  deserialize
    | "Conjunction" => Connective.conjunction
    | "Disjunction" => Connective.disjunction
    | "Implication" => Connective.implication
    | "Equivalence" => Connective.equivalence
    | "ExclusiveOr" => Connective.exclusiveOr
    | "NegatedDisjunction" => Connective.negatedDisjunction
    | json => throwUnexpected "connective" json

instance : Deserializable Quantifier where
  deserialize
    | "Universally" => Quantifier.universally
    | "Existentially" => Quantifier.existentially
    | "Nonexistentially" => Quantifier.nonexistentially
    | json => throwUnexpected "quantifier" json

instance : Deserializable Bound where
  deserialize (json: Lean.Json) : DeserializeM Bound := match getInductive? json with
    | some ("Unbounded", Lean.Json.null) => Bound.unbounded
    | some ("Bounded", arr #[sgn, rel, expr]) => Bound.bounded
        <$> deserialize sgn
        <*> deserialize rel
        <*> deserialize expr
    | _ => throwUnexpected "bound" json

mutual
  private partial def deserializeNP : Lean.Json -> DeserializeM NounPhrase
    | arr #[adjL, noun, var?, adjR, stmt?] => NounPhrase.mk
        <$> deserialize adjL
        <*> deserialize noun
        <*> deserialize var?
        <*> deserialize adjR
        <*> deserializeStmt stmt?
    | json => throwUnexpected "noun phrase" json

    private partial def deserializeNPVars : Lean.Json -> DeserializeM NounPhraseVars
    | arr #[adjL, noun, vars, adjR, stmt?] => NounPhraseVars.mk
        <$> deserialize adjL
        <*> deserialize noun
        <*> deserialize vars
        <*> deserialize adjR
        <*> deserializeStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def deserializeQPhrase : Lean.Json -> DeserializeM QuantPhrase
    | arr #[quant, np] => QuantPhrase.mk <$> deserialize quant <*> deserializeNPVars np
    | json => throwUnexpected "quantified phrase" json

  private partial def deserializeStmt (json: Lean.Json) : DeserializeM Stmt := match getInductive? json with
    | some ("StmtFormula", t) => Stmt.formula <$> deserialize t
    | some ("StmtVerbPhrase", arr #[term, verbPhrase]) => Stmt.verbPhrase
        <$> deserialize term
        <*> deserialize verbPhrase
    | some ("StmtNoun", arr #[term, np]) => Stmt.noun
        <$> deserialize term
        <*> deserializeNP np
    | some ("StmtNeg", t) => Stmt.neg <$> deserializeStmt t
    | some ("StmtExists", t) => Stmt.exists' <$> deserializeNPVars t
    | some ("StmtConnected", arr #[con, stmt, stmt']) => Stmt.connected
        <$> deserialize con
        <*> deserializeStmt stmt
        <*> deserializeStmt stmt'
    | some ("StmtQuantPhrase", arr #[qPhrase, stmt]) => Stmt.quantPhrase
        <$> deserializeQPhrase qPhrase
        <*> deserializeStmt stmt
    | some ("SymbolicQuantified", arr #[qPhrase, varSymbs, bound, suchThat, stmt]) => Stmt.symbolicQuantified
        <$> deserializeQPhrase qPhrase
        <*> deserialize varSymbs
        <*> deserialize bound
        <*> deserializeStmt suchThat
        <*> deserializeStmt stmt
    | _ => throwUnexpected "statement" json
end

instance : Deserializable NounPhrase := mk deserializeNP
instance : Deserializable NounPhraseVars := mk deserializeNPVars
instance : Deserializable QuantPhrase := mk deserializeQPhrase
instance : Deserializable Stmt := mk deserializeStmt

instance : Deserializable DefnHead where
  deserialize json := match getInductive? json with
    | some ("DefnAdj", arr #[np, varSymb, adj]) => DefnHead.adj
        <$> deserialize np
        <*> deserialize varSymb
        <*> deserialize adj
    | some ("DefnVerb", arr #[np, varSymb, verb]) => DefnHead.verb
        <$> deserialize np
        <*> deserialize varSymb
        <*> deserialize verb
    | some ("DefnNoun", arr #[varSymb, noun]) => DefnHead.noun
        <$> deserialize varSymb
        <*> deserialize noun
    | some ("DefnRel", arr #[varSymb, rel, varSymb']) => DefnHead.rel
        <$> deserialize varSymb
        <*> deserialize rel
        <*> deserialize varSymb'
    | some ("DefnSymbolicPredicate", arr #[symbPred, varSymbs]) => DefnHead.symbolicPredicate
        <$> deserialize symbPred
        <*> deserialize varSymbs
    | _ => throwUnexpected "definition head" json

instance : Deserializable Asm where
  deserialize json := match getInductive? json with
    | some ("AsmSuppose", stmt) => Asm.suppose <$> deserialize stmt
    | some ("AsmLetNoun", arr #[vs, np]) => Asm.letNoun
        <$> deserialize vs
        <*> deserialize np
    | some ("AsmLetIn", arr #[vs, expr]) => Asm.letIn
        <$> deserialize vs
        <*> deserialize expr
    | some ("AsmLetThe", arr #[vs, fNoun]) => Asm.letThe
        <$> deserialize vs
        <*> deserialize fNoun
    | some ("AsmLetEq", arr #[vs, expr]) => Asm.letEq
        <$> deserialize vs
        <*> deserialize expr
    | _ => throwUnexpected "assumption" json

instance : Deserializable Defn where
  deserialize json := match getInductive? json with
    | some ("Defn", arr #[asms, defnHead, stmt]) => Defn.defn
        <$> deserialize asms
        <*> deserialize defnHead
        <*> deserialize stmt
    | some ("DefnFun", arr #[asms, fNoun, term?, term]) => Defn.fun'
        <$> deserialize asms
        <*> deserialize fNoun
        <*> deserialize term?
        <*> deserialize term
    | _ => throwUnexpected "definition" json

instance : Deserializable Axiom where
  deserialize json := match getInductive? json with
    | some ("Axiom", arr #[asms, stmt]) => Axiom.mk
        <$> deserialize asms
        <*> deserialize stmt
    | _ => throwUnexpected "axiom" json

instance : Deserializable Lemma where
  deserialize json := match getInductive? json with
    | some ("Lemma", arr #[asms, stmt]) => Lemma.mk
        <$> deserialize asms
        <*> deserialize stmt
    | _ => throwUnexpected "lemma" json

instance : Deserializable Para where
  deserialize json := match getInductive? json with
    | some ("ParaDefn", defn) => Para.defn' <$> deserialize defn
    | some ("ParaLemma", arr #[tag, lem]) => Para.lemma'
        <$> deserialize tag
        <*> deserialize lem
    | _ => throwUnexpected "paragraph" json

-- Wow, removing the monad transformer typeclass from Deserialize
-- improves the compilation time of this from 3:25min to 1.5 sec.
-- It's still a lot, but I can work with it.

-- I guess the problem was that every usage of `deserialize` triggered
-- the typeclass instance problem for the monad transformer, since
-- the monad transformer was a typeclass parameter. But the profiler
-- says that the complexity lied in `compilation` not in
-- `typeclass inference`. I am still not sure what the issue was,
-- but maybe moving the typeclass parameter to an explicit param
-- of `deserialize` would also have solved the issue.

-- set_option profiler true
-- def deserialize' : DeserializeM Para := Deserializable.deserialize null
