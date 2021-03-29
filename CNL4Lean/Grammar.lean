
namespace CNL4Lean

inductive NonEmpty (α : Type u) where
  | singleton : α -> NonEmpty α
  | cons : α -> NonEmpty α -> NonEmpty α

-- `Tokenizer.hs`

inductive Delim where
  | invis : Delim
  | paren : Delim
  | brace : Delim
  | bracket : Delim

-- This doesn't include all tokens, since some kinds are not allowed in `Adapt.hs`
inductive Tok where
  | word : String -> Tok
  | variableT : String -> Tok
  | symbol : String -> Tok
  | integer : Int -> Tok
  | command : String -> Tok
  | openT : Delim -> Tok
  | close : Delim -> Tok

abbrev Pattern := List (Option Tok)

-- `Variable.hs`

inductive VarSymbol where
  | namedVar : String -> VarSymbol
  | freshVar : Int -> VarSymbol

-- `Abstract.hs`

-- It seems quite stupid to propagate this information to this lean backend, but I guess I should keep this information for consistency sake and in case I want to let lean output sophisticated error messages.

inductive Symbol where
  -- This constructor is extremely odd. It is used to encode function application. I feel like function application should be
  -- a primitive in `Expr'`. Just like one might add lambda abstraction as a primitive in `Expr'` and also dependent functions.
  | const : Tok -> Symbol
  | mixfix : Pattern -> Symbol

inductive Expr' where
  | var : VarSymbol -> Expr'
  | int : Int -> Expr'
  -- One should maybe consider adding some better static constraints to the lenght of the list...
  | symbol : Symbol -> NonEmpty Expr' -> Expr'

-- A binary relation
abbrev Relator := Tok

inductive Sign where
  | positive : Sign
  | negative : Sign

inductive Chain where
  -- This is simply one relation symbol applied to a bunch of expressions
  | chainBase : NonEmpty Expr' -> Sign -> Relator -> NonEmpty Expr' -> Chain
  -- We can also chain relations:
  | chainCons : NonEmpty Expr' -> Sign -> Relator -> Chain -> Chain

inductive SymbolicPredicate where
  | symbolicPredicate : String -> Int -> SymbolicPredicate

inductive Formula where
  | chain : Chain -> Formula
  | predicate : SymbolicPredicate -> NonEmpty Expr' -> Formula


structure SgPl where
  sg : Pattern
  pl : Pattern

mutual
  -- This can be exploited to parse dependent types.
  -- Like "a function from [x:A] to [b(x):B(x)]", which can be compiled
  -- to the corresponding dependent function.

  -- e.g. "A functor from $C$ to $D$."
  inductive Fun where
    | lexicalPhrase : SgPl -> List Term -> Fun

  -- Note: This does not allow putting functional nouns inside symbolic
  -- expressions
  inductive Term where
    | expr : Expr' -> Term   -- Symbolic version
    | function : Fun -> Term -- Version with words
end

inductive FunSymb where
  | lexicalPhrase : SgPl -> List VarSymbol -> FunSymb

structure Noun where
  -- SEM: A map `A_1 -> ... -> A_{n+1} -> Prop`, where `n` is the number of holes in the pattern.
  -- That would be the variant adding indirection. If we want to avoid adding indirection:
  -- Use proposition with n+1 free variables, then substitute the arguments in directly.

  -- Now claiming that `$x$ is a prime number`, will boil down to using the predicate
  -- `prime : Nat -> Prop` in order to compile the phrase to specify `x:Nat` and get
  -- the proposition `prime x`. This essentially says that the semantics of `Stmt` simply
  -- are propositions in a suitable context of free variables.
  lexicalPhrase : SgPl
  arguments : List Term

structure NounSymb where
  lexicalPhrase : SgPl
  arguments : List VarSymbol

structure Adj where
  -- SEM: See `Noun`.
  arguments : List Term

structure AdjSymb where
  lexicalPhrase : Pattern
  arguments : List VarSymbol

structure Verb where
  -- SEM: See `Noun`.
  lexicalPhrase : SgPl
  arguments : List Term

structure VerbSymb where
  lexicalPhrase : SgPl
  arguments : List VarSymbol

inductive VerbPhrase where
  | vPVerb : Verb -> VerbPhrase
  | vPAdj : Adj -> VerbPhrase
  | vPVerbNot : Verb -> VerbPhrase
  | vPAdjNot : Adj -> VerbPhrase

structure AdjL extends Adj

inductive AdjR where
  | adjR : Pattern -> List Term -> AdjR
  | attrRThat : VerbPhrase -> AdjR

inductive Connective where
  | conjunction
  | disjunction
  | implication
  | equivalence
  | exclusiveOr
  | negatedDisjunction

inductive Quantifier where
  | universally
  | existentially
  | nonexistentially

-- We probably won't need this.
inductive Bound where
  | Unbounded
  | Bounded

mutual
  -- SEM: Essentially it is a sigma type, only that for the sake of proof irrelevance,
  -- we carry the 
  inductive NounPhrase where
    | nounPhrase : AdjL -> Noun -> Option VarSymbol -> AdjR -> Option Stmt -> NounPhrase

  inductive NounPhraseVars where
    | nounPhrase : AdjL -> Noun -> List VarSymbol -> AdjR -> Option Stmt -> NounPhraseVars
  
  inductive QuantPhrase where
    | qPhrase : Quantifier -> NounPhraseVars -> QuantPhrase
  
  inductive Stmt where
    | formula : Formula -> Stmt
    | verbPhrase : Term -> VerbPhrase -> Stmt
    | noun : Term -> NounPhrase -> Stmt
    | neg : Stmt
    | exists' : NounPhraseVars -> Stmt
    | connected : Connective -> Stmt -> Stmt -> Stmt
    | quantPhrase : QuantPhrase -> Stmt -> Stmt
    | symbolicQuantified : QuantPhrase -> NonEmpty VarSymbol -> Bound -> Option Stmt -> Stmt
end

inductive DefnHead where
  | adj : Option NounPhrase -> VarSymbol -> AdjSymb -> DefnHead
  | verb : Option NounPhrase -> VarSymbol -> VerbSymb -> DefnHead
  | noun : VarSymbol -> NounSymb -> DefnHead
  | rel : VarSymbol -> Relator -> VarSymbol -> DefnHead
  | symbolicPredicate : SymbolicPredicate -> NonEmpty VarSymbol -> DefnHead

inductive Asm where
  | suppose : Stmt -> Asm
  | letNoun : NonEmpty VarSymbol -> NounPhrase -> Asm
  -- I probably don't want to allow this? This is an element sign
  | letIn : NonEmpty VarSymbol -> Expr' -> Asm
  | letThe : VarSymbol -> Fun -> Asm
  | letEq : VarSymbol -> Expr' -> Asm

inductive Defn where
  | defn : List Asm -> DefnHead -> Stmt -> Defn
  | defnFun : List Asm -> Fun -> Option Term -> Term -> Defn

structure Axiom where
  asms : List Asm
  stmt : Stmt

structure Lemma where
  asms : List Asm
  stmt : Stmt

abbrev Tag := Option (List Tok)

inductive Para where
  | defnP : Defn -> Para
  | axiomP : Tag -> Axiom -> Para
  | lemmaP : Tag -> Lemma -> Para
