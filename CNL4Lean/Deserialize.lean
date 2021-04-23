
import CNL4Lean.Grammar
import Lean


namespace CNL4Lean
-- This is a painfully boring deserialization module.

open Lean


-- I may not need this..
def toExcept {α: Type u} {ε: Type v} (opt: Option α) (err: ε) : Except ε α := match opt with
  | some x => x
  | none => Except.error err

inductive DeserializationError where
  | unexpectedValue : String -> Json -> DeserializationError
  | unsupportedFeature : String -> DeserializationError
  | parsingError : String -> DeserializationError

open DeserializationError

instance : Inhabited DeserializationError where
  default := unexpectedValue "" Json.null

instance : ToString DeserializationError where
  toString
    | unexpectedValue expected json => s!"Expected a json value of type '{expected}', got '{json.compress}'."
    | unsupportedFeature feature => s!"The lean backend does not support {feature}"
    | parsingError msg => s!"Pasing error: {msg}"

def throwUnexpected {α: Type u} {m: Type u -> Type v} [MonadExcept DeserializationError m] (s: String) (json: Json) : m α :=
  throw (unexpectedValue s json)

class Deserializable (α: Type u) (m: Type u -> Type v) [MonadExcept DeserializationError m] where
  deserialize : Json -> m α

open Deserializable

section Deserializable

variable [Monad m] [MonadExcept DeserializationError m]

-- In order to implement `partial`, lean needs to prove that the partial
-- functions we are constructing actually have a total implementation.
-- We provide this implementation implicitly by providing `Inhabited`.
instance : Inhabited (m α) where
  default := throw arbitrary

instance [Deserializable α m] : Deserializable (Array α) m where
  deserialize
    | Json.arr a => a.mapM deserialize
    | json => throwUnexpected "array" json


instance [Deserializable α m] : Deserializable (Option α) m where
  deserialize
    | Json.null => none
    | json => some <$> deserialize json

-- We provide this instance in order to temporarily use do notation for
-- `Option`.
private instance : Monad Option where
  pure := some
  bind opt f := match opt with
    | none => none
    | some t => f t

/- Gets an inductive type constructor name and its arguments in Json format.
For zero arguments, we return `Json.null`
For one argument we return the json value of the argument,
and for multiple arguments, we return a json array of json values -/
def getInductive? (json : Json) : Option (String × Json) := match json with
  | Json.str s => some (s, Json.null)
  | json => getInductiveArgs? json
where
  getInductiveArgs? (json : Json) : Option (String × Json) := do
    let tag <- json.getObjVal? "tag"
    let tag <- tag.getStr?
    let contents <- json.getObjVal? "contents"
    (tag, contents)


instance : Deserializable Delim m where
  deserialize
    | "Invis" => Delim.invis
    | "Paren" => Delim.invis
    | "Brace" => Delim.invis
    | "Bracket" => Delim.invis
    | json => throwUnexpected "delimiter" json


instance : Deserializable Tok m where
  deserialize json := match getInductive? json with
    | some ("Word", Json.str t) => Tok.word t
    | some ("Variable", Json.str t) => Tok.variable' t
    | some ("Symbol", Json.str t) => Tok.symbol t
    | some ("Integer", (n: Int)) => Tok.integer n
    | some ("Command", Json.str t) => Tok.command t
    | some ("Open", t) => Tok.open' <$> deserialize t
    | some ("Close", t) => Tok.close <$> deserialize t
    | _ => throwUnexpected "token" json


instance : Deserializable VarSymbol m where
  deserialize json := match getInductive? json with
    | some ("NamedVar", Json.str t) => VarSymbol.namedVar t
    | some ("FreshVar", (n: Int)) => VarSymbol.freshVar n
    | _ => throwUnexpected "variable symbol" json


private partial def deserializeExpr (json: Json) : m Expr' := match getInductive? json with
    | some ("ExprVar", varSymb) => Expr'.var <$> deserialize varSymb
    | some ("ExprInteger", (n : Int)) => Expr'.int n
    | some ("ExprConst", t) => Expr'.const <$> deserialize t
    | some ("ExprMixfix", Json.arr #[pattern, Json.arr args]) => do
      let pattern <- deserialize pattern
      let args <- args.mapM deserializeExpr
      Expr'.mixfix pattern args
    | _ => throwUnexpected "expression" json

instance : Deserializable Expr' m where
  deserialize := deserializeExpr

instance : Deserializable Sign m where
  deserialize
    | "Positive" => Sign.positive
    | "Negative" => Sign.negative
    | json => throwUnexpected "sign" json


private partial def deserializeChain (json: Json) : m Chain := match getInductive? json with
  | some ("ChainBase", Json.arr #[Json.arr leftExprs, sgn, rel, Json.arr rightExprs]) => do
    let leftExprs <- leftExprs.mapM deserialize
    let sgn <- deserialize sgn
    let rel <- deserialize rel
    let rightExprs <- rightExprs.mapM deserialize
    Chain.chainBase leftExprs sgn rel rightExprs
  | some ("ChainCons", Json.arr #[Json.arr leftExprs, sgn, rel, chain]) => do
    let leftExprs <- leftExprs.mapM deserialize
    let sgn <- deserialize sgn
    let rel <- deserialize rel
    let chain <- deserializeChain chain
    Chain.chainCons leftExprs sgn rel chain
  | _ => throwUnexpected "chain" json


instance : Deserializable Chain m where
  deserialize := deserializeChain

instance : Deserializable SymbolicPredicate m where
  deserialize
    | Json.arr #[Json.str pred, (arity : Int)] => SymbolicPredicate.mk pred arity
    | json => throwUnexpected "symbolic predicate" json

instance : Deserializable Formula m where
  deserialize (json: Json) : m Formula := match getInductive? json with
  | some ("FormulaChain", t) => Formula.chain <$> deserialize t
  | some ("FormulaPredicate", Json.arr #[pred, Json.arr args]) =>       
    Formula.predicate <$> deserialize pred <*> args.mapM deserialize
  | _ => throwUnexpected "formula" json

instance : Deserializable SgPl m where
  deserialize (json: Json) : m SgPl := do
    let sg <- match json.getObjVal? "sg" with
      | some sg => deserialize sg
      | none => throwUnexpected "SgPl" json
    
    let pl <- match json.getObjVal? "pl" with
      | some pl => deserialize pl
      | none => throwUnexpected "SgPl" json
    
    pure { sg := sg, pl := pl }

mutual
  partial def deserializeTerm (json: Json): m Term := match getInductive? json with
    | some ("TermExpr", t) => Term.expr <$> deserialize t
    | some ("TermFun", t) => Term.function <$> deserializeFun t
    | _ => throwUnexpected "term" json

  partial def deserializeFun : Json -> m Fun
    | Json.arr #[sgPl, Json.arr args] => Fun.mk <$> deserialize sgPl <*> args.mapM deserializeTerm'
    | json => throwUnexpected "functional noun" json
  where
    -- This is a workaround for a bug, where the lean kernel doesn't find 
    -- the `deserializedTerm` namespace when passed to `mapM`
    deserializeTerm' := deserializeTerm
end

instance : Deserializable Fun m where
  deserialize := deserializeFun

instance : Deserializable Term m where
  deserialize := deserializeTerm

instance [Deserializable α m]: Deserializable (Noun α) m where
  deserialize
    | Json.arr #[sgPl, Json.arr args] =>
      Noun.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "noun" json

instance [Deserializable α m]: Deserializable (Adj α) m where
  deserialize
    | Json.arr #[sgPl, Json.arr args] =>
      Adj.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "adjective" json

instance [Deserializable α m]: Deserializable (Verb α) m where
  deserialize
    | Json.arr #[sgPl, Json.arr args] =>
      Verb.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "verb" json

instance : Deserializable VerbPhrase m where
  deserialize (json: Json) : m VerbPhrase := match getInductive? json with
    | some ("VPVerb", t) => VerbPhrase.verb <$> deserialize t
    | some ("VPAdj", t) => VerbPhrase.adj <$> deserialize t
    | some ("VPVerbNot", t) => VerbPhrase.verbNot <$> deserialize t
    | some ("VPAdjNot", t) => VerbPhrase.adjNot <$> deserialize t
    | _ => throwUnexpected "verb phrase" json

instance : Deserializable AdjL m where
  deserialize
    | Json.arr #[sgPl, Json.arr args] =>
      AdjL.mk <$> deserialize sgPl <*> args.mapM deserialize
    | json => throwUnexpected "left adjective" json

instance : Deserializable AdjR m where
  deserialize (json: Json) : m AdjR := match getInductive? json with
    | some ("AdjR", Json.arr #[sgPl, Json.arr args]) =>
      AdjR.adjR <$> deserialize sgPl <*> args.mapM deserialize
    | _ => throwUnexpected "right adjective" json

instance : Deserializable Connective m where
  deserialize
    | "Conjunction" => Connective.conjunction
    | "Disjunction" => Connective.disjunction
    | "Implication" => Connective.implication
    | "Equivalence" => Connective.equivalence
    | "ExclusiveOr" => Connective.exclusiveOr
    | "NegatedDisjunction" => Connective.negatedDisjunction
    | json => throwUnexpected "connective" json

instance : Deserializable Quantifier m where
  deserialize
    | "Universally" => Quantifier.universally
    | "Existentially" => Quantifier.existentially
    | "Nonexistentially" => Quantifier.nonexistentially
    | json => throwUnexpected "quantifier" json

instance : Deserializable Bound m where
  deserialize (json: Json) : m Bound := match getInductive? json with 
    | some ("Unbounded", Json.null) => Bound.unbounded
    | some ("Bounded", Json.arr #[sgn, rel, expr]) => Bound.bounded
        <$> deserialize sgn
        <*> deserialize rel
        <*> deserialize expr
    | _ => throwUnexpected "bound" json

mutual
  private partial def deserializeNP : Json -> m NounPhrase
    | Json.arr #[adjL, noun, var?, adjR, stmt?] => NounPhrase.mk
        <$> deserialize adjL
        <*> deserialize noun
        <*> deserialize var?
        <*> deserialize adjR
        <*> deserializeStmt stmt?
    | json => throwUnexpected "noun phrase" json
  
    private partial def deserializeNPVars : Json -> m NounPhraseVars
    | Json.arr #[adjL, noun, vars, adjR, stmt?] => NounPhraseVars.mk
        <$> deserialize adjL
        <*> deserialize noun
        <*> deserialize vars
        <*> deserialize adjR
        <*> deserializeStmt stmt?
    | json => throwUnexpected "noun phrase" json

  private partial def deserializeQPhrase : Json -> m QuantPhrase
    | Json.arr #[quant, np] => QuantPhrase.mk <$> deserialize quant <*> deserializeNPVars np
    | json => throwUnexpected "quantified phrase" json

  private partial def deserializeStmt (json: Json) : m Stmt := match getInductive? json with
    | some ("StmtFormula", t) => Stmt.formula <$> deserialize t
    | some ("StmtVerbPhrase", Json.arr #[term, verbPhrase]) => Stmt.verbPhrase
        <$> deserialize term
        <*> deserialize verbPhrase
    | some ("StmtNoun", Json.arr #[term, np]) => Stmt.noun
        <$> deserialize term
        <*> deserializeNP np
    | some ("StmtNeg", t) => Stmt.neg <$> deserializeStmt t
    | some ("StmtExists", t) => Stmt.exists' <$> deserializeNPVars t
    | some ("StmtConnected", Json.arr #[con, stmt, stmt']) => Stmt.connected
        <$> deserialize con
        <*> deserializeStmt stmt
        <*> deserializeStmt stmt'
    | some ("StmtQuantPhrase", Json.arr #[qPhrase, stmt]) => Stmt.quantPhrase
        <$> deserializeQPhrase qPhrase
        <*> deserializeStmt stmt
    | some ("SymbolicQuantified", Json.arr #[qPhrase, varSymbs, bound, suchThat, stmt]) => Stmt.symbolicQuantified
        <$> deserializeQPhrase qPhrase
        <*> deserialize varSymbs
        <*> deserialize bound
        <*> deserializeStmt suchThat
        <*> deserializeStmt stmt
    | _ => throwUnexpected "statement" json
end

instance : Deserializable NounPhrase m where
  deserialize := deserializeNP

instance : Deserializable NounPhraseVars m where
  deserialize := deserializeNPVars

instance : Deserializable QuantPhrase m where
  deserialize := deserializeQPhrase

instance : Deserializable Stmt m where
  deserialize := deserializeStmt

instance : Deserializable DefnHead m where
  deserialize json := match getInductive? json with
    | some ("DefnAdj", Json.arr #[np, varSymb, adj]) => DefnHead.adj
        <$> deserialize np
        <*> deserialize varSymb
        <*> deserialize adj
    | some ("DefnVerb", Json.arr #[np, varSymb, verb]) => DefnHead.verb
        <$> deserialize np
        <*> deserialize varSymb
        <*> deserialize verb
    | some ("DefnNoun", Json.arr #[varSymb, noun]) => DefnHead.noun
        <$> deserialize varSymb
        <*> deserialize noun
    | some ("DefnRel", Json.arr #[varSymb, rel, varSymb']) => DefnHead.rel
        <$> deserialize varSymb
        <*> deserialize rel
        <*> deserialize varSymb'
    | some ("DefnSymbolicPredicate", Json.arr #[symbPred, varSymbs]) => DefnHead.symbolicPredicate
        <$> deserialize symbPred
        <*> deserialize varSymbs
    | _ => throwUnexpected "definition head" json

instance : Deserializable Asm m where
  deserialize json := match getInductive? json with
    | some ("AsmSuppose", stmt) => Asm.suppose <$> deserialize stmt
    | some ("AsmLetNoun", Json.arr #[vs, np]) => Asm.letNoun
        <$> deserialize vs
        <*> deserialize np
    | some ("AsmLetIn", Json.arr #[vs, expr]) => Asm.letIn
        <$> deserialize vs
        <*> deserialize expr
    | some ("AsmLetThe", Json.arr #[vs, fNoun]) => Asm.letThe
        <$> deserialize vs
        <*> deserialize fNoun
    | some ("AsmLetEq", Json.arr #[vs, expr]) => Asm.letEq
        <$> deserialize vs
        <*> deserialize expr
    | _ => throwUnexpected "assumption" json

instance : Deserializable Defn m where
  deserialize json := match getInductive? json with
    | some ("Defn", Json.arr #[asms, defnHead, stmt]) => Defn.defn
        <$> deserialize asms
        <*> deserialize defnHead
        <*> deserialize stmt
    | some ("DefnFun", Json.arr #[asms, fNoun, term?, term]) => Defn.fun'
        <$> deserialize asms
        <*> deserialize fNoun
        <*> deserialize term?
        <*> deserialize term
    | _ => throwUnexpected "definition" json

instance : Deserializable Axiom m where
  deserialize json := match getInductive? json with
    | some ("Axiom", Json.arr #[asms, stmt]) => Axiom.mk
        <$> deserialize asms
        <*> deserialize stmt
    | _ => throwUnexpected "axiom" json

instance : Deserializable Lemma m where
  deserialize json := match getInductive? json with
    | some ("Lemma", Json.arr #[asms, stmt]) => Lemma.mk
        <$> deserialize asms
        <*> deserialize stmt
    | _ => throwUnexpected "lemma" json

instance : Deserializable Para m where
  deserialize json := match getInductive? json with
    | some ("ParaDefn", defn) => Para.defn' <$> deserialize defn
    | some ("ParaLemma", Json.arr #[tag, lem]) => Para.lemma'
        <$> deserialize tag
        <*> deserialize lem
    | _ => throwUnexpected "paragraph" json

end Deserializable

abbrev DeserializeM := ExceptT DeserializationError IO