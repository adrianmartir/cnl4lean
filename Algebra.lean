
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

-- Do we want to be able to coerce monoids to semigroups?
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

notation:max "⁻¹" arg  => powMinusOne arg

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

class Commutative (X : SemigroupStr) where
  comm : forall x y : X, x ∘ y = y ∘ x

class Associative (X: SemigroupStr) where
  assoc : forall x y z: X, (x ∘ y) ∘ z = x ∘ (y ∘ z)

class LeftIdentity (X: MonoidStr) where
  leftId : forall x, X.id ∘ x = x

class RightIdentity (X: MonoidStr) where
  rightId : forall x, x ∘ X.id = x

class RightInverse (X: GroupStr) where
  rightInv : forall x, x ∘ X.inv x = X.id

class LeftInverse (X: GroupStr) where
  leftInv : forall x, X.inv x ∘ x = X.id

----------
-- We implement properties with type classes!
class IsMonoid (X: MonoidStr) extends Associative X.toSemigroupStr, LeftIdentity X, RightIdentity X where

class IsGroup (X: GroupStr) extends IsMonoid X.toMonoidStr where
  leftInv : LeftInverse X
  rightInverse : RightInverse X

-- 1. Construction.
-- This should be fairly natural:
-- `\begin{definition}`
-- `Define $G$ to be the group structure ... on $X$.`
-- `\end{definition}`
-- (This should have an automatic coercion to type)
-- Then:
-- `\begin{lemma} \instance`
-- `$G$ is a group.`
-- `\end{lemma}`

-- 2. Usage.
-- `Let $G$ be a group.` should be interpreted adding to the context `G: GroupStr` and
-- `IsGroup G`.

-- I think handling properties as typeclasses is good, because there are many properties
-- that are constructed ad-hoc. Like `irreducible, finite monoid $m$`. We would like to
-- automatically throw away excess properties when passing `$m$` to a function that maybe
-- only expects a semigroup. This linguistic shuffling around of adjectives and properties must be automated
-- in order to get a reasonable interface. And the only tool available are typeclasses.


-- Hm, can we do this?
-- def inverseFromExistence (X: MonoidStr) (p: forall x, exists y: X, x ∘ y = X.id) : GroupStr := by
--   apply GroupStr.mk
