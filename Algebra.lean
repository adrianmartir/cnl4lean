
-- https://jiggerwit.wordpress.com/2018/09/18/a-review-of-the-lean-theorem-prover/
-- An actual, unparameterized, structure
-- This better fits natural language.
structure SemigroupStr where
  obj: Type u
  op: obj -> obj -> obj

structure MonoidStr extends SemigroupStr where
  id: obj

structure GroupStr extends MonoidStr where
  inv: obj -> obj

-- Extends lets us easly use metaprogramming to compute lists of
-- elements for structures.

instance : CoeSort SemigroupStr (Type u) where
  coe x := x.obj

instance : CoeSort MonoidStr (Type u) where
  coe x := x.obj

instance : CoeSort GroupStr (Type u) where
  coe x := x.obj

------------------
namespace Notation
-- Separate notation module(completely optional!!)
-- This is done for instance in order to specify manually whether we
-- want an additive or a multiplicative group.

class CircNotation (α: Type u) where
  circ: α -> α -> α

open CircNotation

notation:80 lhs " ∘ " rhs:81  => circ rhs lhs

class PlusNotation (α: Type u) where
  plus: α -> α -> α

open PlusNotation

notation:30 lhs " + " rhs:31  => plus rhs lhs

class PowMinusOne (α: Type u) where
  powMinusOne: α -> α

open PowMinusOne

notation:max "⁻¹" arg  => minus arg

class Minus (α: Type u) where
  minus: α -> α

open Minus

notation:95 "-" arg  => minus arg

-- Implementations
-- Notation is separate from structure!!
instance (X: SemigroupStr) : CircNotation X.obj where
  circ := X.op

instance (X: GroupStr) : CircNotation X.obj where
  circ := X.op

end Notation
----------------

open Notation

abbrev Commutative (X : SemigroupStr) := forall x y : X, x ∘ y = y ∘ x

abbrev Associative (X: SemigroupStr) := forall x y z: X, (x ∘ y) ∘ z = x ∘ (y ∘ z)

abbrev LeftIdentity (X: MonoidStr) := forall x, X.id ∘ x = x
abbrev RightIdentity (X: MonoidStr) := forall x, x ∘ X.id = x

abbrev RightInverse (X: GroupStr) := forall x, x ∘ X.inv x = X.id
abbrev LeftInverse (X: GroupStr) := forall x, X.inv x ∘ x = X.id

----------
-- We implement properties with type classes!
abbrev IsMonoid (X: MonoidStr) :=
  Associative X.toSemigroupStr ∧ LeftIdentity X ∧ RightIdentity X

abbrev IsGroup (X: GroupStr) :=
  IsMonoid X.toMonoidStr ∧ LeftInverse X ∧ RightInverse X

-- It seems that structures have an automatic `Prop -> Type` coercion.
structure Group where
  X: GroupStr
  p: IsGroup X

-- `Let $G$ be a group. Then [...]` should define a function
-- `G: Group -> ?m`, where `[...]` can access
-- the group by using the `$G$` binding.

-- This is useful if `[...]` is something like
-- `The group cohomology of $G$.`,
-- which needs `$G$` to be an actual group instead of only group
-- structure.

-- The difference between propositions and types only comes into play
-- when constructing groups. I would like to do something like:

-- `Define the group structure $G$ on $X$ to be .....`
-- `Lemma. $G$ is a group.`

-- Hm, can we do this?
-- def inverseFromExistence (X: MonoidStr) (p: forall x, exists y: X, x ∘ y = X.id) : GroupStr := by
--   apply GroupStr.mk

-- Hm, I guess one can get composition without typeclasses.... Maybe? This will take experimentation
-- def compose {G: SemigroupStr} (g h: G) := g ∘ h
-- #check compose

-- def naturals: SemigroupStr where
--   obj := Nat
--   op := Nat.add

-- #check naturals.obj
-- #check naturals.op 4 5
