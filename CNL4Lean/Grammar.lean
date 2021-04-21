
namespace CNL4Lean


-- We want the abstract grammar to be as general as Adrian's `Abstract.hs` or even
-- more general. The reason is, that we don't want the deserialization process the option
-- to give out errors that are not merely deserialization errors.

-- If this is ever going to be a finished product, one should also propagate position
-- information for debugging to here.

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

abbrev Pattern := Array (Option Tok)


-- `Variable.hs`

inductive VarSymbol where
  | namedVar : String -> VarSymbol
  | freshVar : Int -> VarSymbol


-- `Abstract.hs`

inductive Expr' where
  | var : VarSymbol -> Expr'
  | int : Int -> Expr'
  | const : Tok -> Expr'
  | mixfix : Pattern -> Array Expr' -> Expr'
  | app : Expr' -> Expr' -> Expr'

-- A binary relation
abbrev Relator := Tok

inductive Sign where
  | positive : Sign
  | negative : Sign

inductive Chain where
  -- This is simply one relation symbol applied to a bunch of expressions
  | chainBase : Array Expr' -> Sign -> Relator -> Array Expr' -> Chain
  -- We can also chain relations:
  | chainCons : Array Expr' -> Sign -> Relator -> Chain -> Chain

inductive SymbolicPredicate where
  | symbolicPredicate : String -> Int -> SymbolicPredicate

inductive Formula where
  | chain : Chain -> Formula
  | predicate : SymbolicPredicate -> Array Expr' -> Formula


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
    | lexicalPhrase : SgPl -> Array Term -> Fun

  -- Note: This does not allow putting functional nouns inside symbolic
  -- expressions
  inductive Term where
    | expr : Expr' -> Term   -- Symbolic version
    | function : Fun -> Term -- Version with words
end

structure lexicalPhrase where 

-- This should also be usable for making type-declaration aliases.
-- and for other kinds of aliases.
inductive Noun (α: Type u) where
  | noun : SgPl -> Array α -> Noun α
  -- The `lexicalPhrase` is a map `A_1 -> ... -> A_n -> B -> Prop`, where `n` is the number of holes in the pattern.
  -- Then the semantics of the hole insert those arguments, so a noun would interpret
  -- to a term of `B -> Prop`. The last argument will get inserted by `Stmt`.
  
  -- That would be the variant adding indirection. If we want to avoid adding indirection:
  -- Use proposition with n+1 free variables, then substitute the arguments in directly.

  -- Now claiming that `$x$ is a prime number`, will boil down to using the predicate
  -- `prime : Nat -> Prop` in order to compile the phrase to specify `x:Nat` and get
  -- the proposition `prime x`. This essentially says that the semantics of `Stmt` simply
  -- are propositions in a suitable context of free variables.
  -- The identifier is for the purposes of refering to this construct from lean.

inductive Adj (α: Type u) where
  -- SEM: See `Noun`.
  | adj : Pattern -> Array α -> Adj α

inductive Verb (α : Type u) where
  -- SEM: See `Noun`.
  | verb : SgPl ->  Array Term -> Verb α

inductive VerbPhrase where
  | verb : Verb Term -> VerbPhrase
  | adj : Adj Term -> VerbPhrase
  | verbNot : Verb Term -> VerbPhrase
  | adjNot : Adj Term -> VerbPhrase

inductive AdjL where
  | adjL : Pattern -> Array Term -> AdjL

inductive AdjR where
  | adjR : Adj Term -> AdjR
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
    | nounPhrase : AdjL -> Noun Term -> Option VarSymbol -> AdjR -> Option Stmt -> NounPhrase

  inductive NounPhraseVars where
    | nounPhrase : AdjL -> Noun Term -> Array VarSymbol -> AdjR -> Option Stmt -> NounPhraseVars
  
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
    | symbolicQuantified : QuantPhrase -> Array VarSymbol -> Bound -> Option Stmt -> Stmt
end

inductive DefnHead where
  | adj : Option NounPhrase -> VarSymbol -> Adj VarSymbol -> DefnHead
  | verb : Option NounPhrase -> VarSymbol -> Verb VarSymbol -> DefnHead
  | noun : VarSymbol -> Noun VarSymbol-> DefnHead
  | rel : VarSymbol -> Relator -> VarSymbol -> DefnHead
  | symbolicPredicate : SymbolicPredicate -> Array VarSymbol -> DefnHead

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
  -- where the types are only partially defined, like `Array ?m`. In fact, with this trick,
  -- we can accept typing declarations anywhere in the grammatical tree.
  | letNoun : Array VarSymbol -> NounPhrase -> Asm
  -- A typing declaration.
  | letIn : Array VarSymbol -> Expr' -> Asm
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
  | defn : Array Asm -> DefnHead -> Stmt -> Defn
  | defnFun : Array Asm -> Fun -> Option Term -> Term -> Defn

structure Axiom where
  -- Assumptions should be read sequentially in order to modify the local context
  -- recursively in order to finally read the `stmt`. Finally the assumptions get
  -- wrapped into a local binding.
  asms : Array Asm
  stmt : Stmt

structure Lemma where
  asms : Array Asm
  stmt : Stmt

abbrev Tag := Option (Array Tok)

inductive Para where
  | defnP : Defn -> Para
  | axiomP : Tag -> Axiom -> Para
  | lemmaP : Tag -> Lemma -> Para
