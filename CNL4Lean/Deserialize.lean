
import CNL4Lean.Grammar
import Lean


namespace CNL4Lean
-- This is a painfully boring deserialization module.

open Lean

-- #check IO.FS.readFile
#check Json.parse
#check Json.Parser.any


-- I may not need this..
def toExcept {α: Type u} {ε: Type v} (opt: Option α) (err: ε) : Except ε α := match opt with
  | some x => x
  | none => Except.error err

inductive DeserializationError where
  | unexpected : String -> Json -> DeserializationError
  | unsupportedFeature : String -> DeserializationError
  | parsingError : String -> DeserializationError

open DeserializationError

instance : Inhabited DeserializationError where
  default := unexpected "" Json.null

def asString
  | unexpected expected json => s!"Expected a {expected}, got {json.compress}."
  | unsupportedFeature feature => s!"The lean backend does not support {feature}"
  | parsingError msg => s!"Pasing error: {msg}"

def throwUnexpected {α: Type u} {m: Type u -> Type v} [MonadExcept DeserializationError m] (s: String) (json: Json) : m α :=
  throw (unexpected s json)

-- Except (from `Prelude.lean`) has the MonadExept instance and there are transformers for it (see `Init/Control/Except.lean`)
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


def getInductive? (json : Json) : Option (String × Json) := do
  let tag <- json.getObjVal? "tag"
  let tag <- json.getStr?

  let contents <- json.getObjVal? "contents"
  (tag, contents)


instance : Deserializable Delim m where
  deserialize
    | Json.str "Invis" => Delim.invis
    | Json.str "Paren" => Delim.invis
    | Json.str "Brace" => Delim.invis
    | Json.str "Bracket" => Delim.invis
    | json => throwUnexpected "delimiter" json


instance : Deserializable Tok m where
  deserialize json := match getInductive? json with
    | some ("Word", Json.str t) => Tok.word t
    | some ("Variable", Json.str t) => Tok.variableT t
    | some ("Symbol", Json.str t) => Tok.symbol t
    | some ("Integer", (n: Int)) => Tok.integer n
    | some ("Command", Json.str t) => Tok.command t
    | some ("Open", t) => Tok.openT <$> deserialize t
    | some ("Close", t) => Tok.close <$> deserialize t
    | _ => throwUnexpected "token" json


instance : Deserializable VarSymbol m where
  deserialize json := match getInductive? json with
    | some ("NamedVar", Json.str t) => VarSymbol.namedVar t
    | some ("FreshVar", (n: Int)) => VarSymbol.freshVar n
    | _ => throwUnexpected "variable symbol" json


partial def deserializeExpr (json: Json) : m Expr' := match getInductive? json with
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
    | Json.str "Positive" => Sign.positive
    | Json.str "Negative" => Sign.negative
    | json => throwUnexpected "sign" json


partial def deserializeChain (json: Json) : m Chain := match getInductive? json with
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

end Deserializable

#check ExceptT

abbrev DeserializeM := ExceptT DeserializationError IO

--IO (Except String (Except DeserializationError a))

def f : DeserializeM Int := throw (unsupportedFeature "")

-- At some point later, in the CLI interface or sth:
def file [Monad m] [MonadLiftT IO m] : m String := IO.FS.readFile "chain.json"

def file' : IO String := file

def json : DeserializeM Json := do
  let contents <- file
  -- How cool! `MonadLiftT` is automatically used!
  match Json.parse contents with
    | Except.ok json => json
    | Except.error msg => throw (parsingError msg)

