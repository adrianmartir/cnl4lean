
namespace CNL4Lean


-- We want the abstract grammar to be as general as Adrian's `Abstract.hs` or even
-- more general. The reason is, that we don't want the deserialization process the option
-- to give out errors that are not merely deserialization errors.

-- If this is ever going to be a finished product, one should also propagate position
-- information for debugging to here.

inductive NonEmpty (α : Type u) where
  | singleton : α -> NonEmpty α
  | cons : α -> NonEmpty α -> NonEmpty α

def NonEmpty.toArray {α : Type u} (nonempty : NonEmpty α) : Array α := sorry

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
  -- I added this `app` here myself since it follows the abstract syntax tree more closely.
  | app : Expr' -> Expr' -> Expr'

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
  -- Actually, that is not true. If I define the semantics
  -- by using 'patterns as functions', then the patterns
  -- must add indirection, so this doesn't work. At some point we
  -- probably want patterns(for `Expr'` and for `Fun`) that don't add indirection, so this
  -- idea is possible.

  -- e.g. "A functor from $C$ to $D$."
  inductive Fun where
    | lexicalPhrase : SgPl -> List Term -> Fun

  -- Note: This does not allow putting functional nouns inside symbolic
  -- expressions
  inductive Term where
    | expr : Expr' -> Term   -- Symbolic version
    | function : Fun -> Term -- Version with words
end

-- This should also be usable for making type-declaration aliases.
-- and for other kinds of aliases.
structure Noun where
  -- The `lexicalPhrase` is a map `A_1 -> ... -> A_n -> B -> Prop`, where `n` is the number of holes in the pattern.
  -- Then the semantics of the hole insert those arguments, so a noun would interpret
  -- to a term of `B -> Prop`. The last argument will get inserted by `Stmt`.
  
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
  -- Interprets to an expression `p` of type `?b -> Prop`.
  inductive NounPhrase where
    | nounPhrase : AdjL -> Noun -> Option VarSymbol -> AdjR -> Option Stmt -> NounPhrase

  inductive NounPhraseVars where
    | nounPhrase : AdjL -> Noun -> List VarSymbol -> AdjR -> Option Stmt -> NounPhraseVars
  
  inductive QuantPhrase where
    | qPhrase : Quantifier -> NounPhraseVars -> QuantPhrase
  
  -- Interprets to an expression of type `Prop`. Note that we could technically also allow
  -- more direct, term-based ways for constructing statements and when interpreting we could
  -- simply tell the unifier that the type should be `Prop`.
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

-- All the of these newly declared variables should all have an optional type
-- annotation!
inductive Asm where
  -- This doesn't add new variables, so it simply adds a proposition to the local
  -- context. (and then is wrapped into a forall).
  | suppose : Stmt -> Asm
  -- First add variables with unknown typing declaration `x : ?m`. Then when
  -- interpreting the noun phrase, infer the type.

  -- Note: We want to add a new section to the vocabulary about 'type aliases'. For something
  -- like `an integer` to be directly mapped to `Int`. Then, when expanding `letNoun`, when we
  -- encounter `$e$ an integer`, we run `isDefEqual typeOfe Int`, which should resolve
  -- metavariables constraints. Leans powerful unification then also allows to add
  -- where the types are only partially defined, like `List ?m`. In fact, with this trick,
  -- we can accept typing declarations anywhere in the grammatical tree.
  | letNoun : NonEmpty VarSymbol -> NounPhrase -> Asm
  -- A typing declaration.
  | letIn : NonEmpty VarSymbol -> Expr' -> Asm
  -- A 'let x := e in B(x)' declaration.
  -- Map to a lean-internal let expression.
  -- We use this instead of using a forall with an equality axiom because in this case
  -- we even have definitional equality.
  | letThe : VarSymbol -> Fun -> Asm
  -- A 'let x := e in B(x)' declaration.
  -- Map to a lean-internal let expression.
  -- We should consider modifying this type in the parser so that it reflects the
  -- assumption that the left hand side is a variable.
  | letEq : VarSymbol -> Expr' -> Asm

inductive Defn where
  -- This should behave like a telescope. I need to rerun `MetaM` after unpacking each
  -- and every assumption recursively.
  | defn : List Asm -> DefnHead -> Stmt -> Defn
  | defnFun : List Asm -> Fun -> Option Term -> Term -> Defn

structure Axiom where
  -- Assumptions should be read sequentially in order to modify the local context
  -- recursively in order to finally read the `stmt`. Finally the assumptions get
  -- wrapped into a local binding.
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
