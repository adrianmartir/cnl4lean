-- Some basic category-theoretic constructions
namespace category_theory

universe u
universe v
universe w

-- This notation is optimal, much better than what was in mathlib.
-- hom sets should always be anotated with the category they are meant
-- to be taken on. Unlike identities and composition operators and axioms.
-- Otherwise we get into typeclass hell when considering opposite categories.
structure hom_struct where
  obj : Type u
  hom : obj → obj → Type v

def hom_struct.opposite (C: hom_struct) : hom_struct := {
  obj := C.obj
  hom := fun f g => C.hom g f
}

notation:1030 arg "ᵒᵖ"  => hom_struct.opposite arg

def hom_struct.op {C: hom_struct} (c: C.obj) : Cᵒᵖ.obj := c
def hom_struct.unop {C: hom_struct} (c: Cᵒᵖ.obj) : C.obj := c

def hom_struct.opm {C: hom_struct} {c d: C.obj} (f : C.hom c d) : Cᵒᵖ.hom d c := f
def hom_struct.unopm {C: hom_struct} {c d: Cᵒᵖ.obj} (f : Cᵒᵖ.hom c d) : C.hom d c := f

attribute [simp] hom_struct.op hom_struct.opm hom_struct.unopm hom_struct.unop

-- I guess typeclasses are easily leveraged in CNL by defining something
-- like an alias `identity -> id'`.
-- Formalizing this definition in CNL is probably not going to happen in my thesis,
-- since there are many, many notational details (typeclasses, implicit arguments)
-- here that don't really fit the CNL style.
class category (C : hom_struct) where
  id' : (c : C.obj) -> C.hom c c
  comp : {c d e : C.obj} -> C.hom c d -> C.hom d e -> C.hom c e
  id_comp : {c d : C.obj} -> (f : C.hom c d) -> ((comp (id' c) f) = f)
  comp_id : {c d : C.obj} -> (f : C.hom c d) -> ((comp f (id' d)) = f)
  assoc : {a b c d : C.obj} -> (f : C.hom a b) -> (g : C.hom b c) -> (h : C.hom c d)
      -> comp (comp f g) h = comp f (comp g h)

notation:80 lhs " ∘ " rhs:81  => category.comp rhs lhs

open hom_struct
open category

attribute [simp] category.id_comp category.comp_id category.assoc

-- https://github.com/leanprover-community/mathlib/blob/8e7028cdc174d5e8083368b86e688bdabbdf3fef/src/category_theory/opposites.lean#L27
-- In mathlib, there were two copies of the same type
-- and by distinguishing between those copies one could disambiguate between
-- `C` and its opposite. This doesn't seem to be possible anymore but I have
-- to say I didn't like it anyways.
instance category.opposite (C: hom_struct) [category C]: category Cᵒᵖ := {
  id' := fun c => hom_struct.opm (id' (hom_struct.unop c))
  comp := fun f g =>
      hom_struct.opm (comp (hom_struct.unopm g) (hom_struct.unopm f))
  id_comp := by
    intros
    simp
  comp_id := by
    intros
    simp
  assoc := by
    intros
    simp
}

notation:1000 arg "ᵒᵖ"  => opposite arg

#check hom_struct

abbrev small_category (C : hom_struct) := category.{u,u} C
abbrev large_category (C : hom_struct) := category.{u+1,u} C

-- It looks a bit odd defining this separately, but it's what you would expect.
-- After all, it is then clear whether you mean `Set` or `Setᵒᵖ`.
def set : hom_struct := {
  obj := Type w,
  hom := fun a b => a -> b
}

instance set.category : large_category set :=
{ id'     := fun a x => x
  comp    := fun f g x => g (f x)
  id_comp := by
    intros
    simp [id', comp]
  comp_id := by
    intros
    simp [id', comp]
  assoc := by
    intros
    simp [comp]
}

-- In CNL, the first two fould simply be symbolic(latex) patterns.
-- The patterns for dependent types are needed here.
-- The latter two would be anonymous. Something like:
-- `Let $C$ be a category. Let $D$ be a category.`
-- According to my previous notes, `category` should desugar to the typing declaratation
-- `category_struct -> Prop`.
-- `A functor from $C$ to $D$ is a ... structure definition`
-- I think that this definition should be done in CNL. I mean, we would have to define
-- the bindings anyways. The implicit arguments could be done with assumptions.
-- There seems to be a lot of complexity added by type parameters. This isn't so easy.
structure functor (C : hom_struct) [category C] (D : hom_struct) [category D] where
  obj : C.obj -> D.obj
  map : {c d : C.obj} -> C.hom c d -> D.hom (obj c) (obj d)
  map_id : {c : C.obj} -> map (id' c) = id' (obj c)
  map_comp : {c d e : C.obj} -> (f : C.hom c d) -> (g : C.hom d e) -> map (g ∘ f) = map g ∘ map f


-- # Structures

-- A natural language structure should consist of
-- 1) A list of parameters
-- 2) A list of constructors
-- 3) A list of properties

-- It should first generate a lean structure for `functor_struct` (which is a type family
-- parameterized by two categories).
-- Then it should consider the property `is_functor: functor_struct -> Prop` on it.

-- `$F$ is a functor from $C$ to $D$.`
-- Yields a `Stmt` with the typed expression `F : functor_struct` and the property
-- `is_functor`. This can be easily inserted into a lemma and proven.
-- We could additionally generate a `functor` struct extending `functor_struct`.

-- For categories, it should be quite different. Doing the same thing as in functor, would
-- yield the statement
-- `$C$ is a category on $X$.` (`X` is a type)
-- We all know that mathematicians like the structure to be implicit and that the natural choice would be:
-- `Let $C$ be a category.`
-- The category pattern should be annotated with the fact that it is a typeclass.
-- In this case `C` should simply be a type, but instead of only having the declaration
-- `C : Type u` in the context, this assertion should also add the typeclass constraint
-- `[category C]` to the the information of `C`.

-- Perhaps a bit surprisingly, the above can only serve as an assumption, and not as a
-- statement. Since a statement like
-- `$C$ is a category.`
-- is nonsensical. One should construct the whole struct in natural language and then
-- claim it forms a category.

-- For the sake of simplicity, I will avoid using typeclasses in CNL for now. The
-- formalization will treat categories as a struct. I also guess that for now
-- arguments should be always explicit.
attribute [simp] functor.map_id functor.map_comp


section nat_trans

variable {C : hom_struct} [category C]
variable {D : hom_struct} [category D]

structure nat_trans (F G : functor C D) :=
  app : (c : C.obj) -> D.hom (F.obj c) (G.obj c)
  naturality : {c d : C.obj} -> (f : C.hom c d) -> app d ∘ (F.map f) = (G.map f) ∘ app c

def functor_cat (C: hom_struct) [category C] (D: hom_struct) [category D]: hom_struct := {
  obj := functor C D
  hom := nat_trans
}

open nat_trans

-- I guess category is full of these things where you simply need
-- to specify a lot of data and prove a lot of properties.
def id_trans (F : functor C D) : nat_trans F F := {
  app := fun c => id' (functor.obj F c),
  naturality := by
    intro c d f
    simp
}

-- In CNL:
-- "\begin{lemma}
--    The family of maps ... is a natural transformation.
--  \end{lemma}"

-- `The [field_name] [Term] [and|,] the [field_name] [Term] ... `
-- Should be a something kind of similar to functional noun and serve as a record
-- constructor.

-- Now one can just claim things like

-- `The type ... and the operation ... are a semigroup.` (`form` instead of `are`?)
-- and completely ignore the fact that there is an inferred type named
-- `semigroup_structure` which is a set equipped with a binary operation.

-- This is honestly extremely cool. Thinking about the linguistic nature of structure.

def vcomp {F G H : functor C D} (η : nat_trans F G) (μ : nat_trans G H) : nat_trans F H := {
  app := fun c => (app μ c) ∘ (app η c),
  naturality := by
    intro c d f
    simp
    rw <- naturality μ f
    rw <- category.assoc
    rw naturality η f
    rw category.assoc
}

theorem nat_ext {F G : functor C D} : (η μ : nat_trans F G) ->(p: η.app = μ.app) -> (η = μ) := by
  intro { app := η, naturality := _ }
  intro { app := μ, naturality := _ }
  intro p
  subst p
  simp

instance functor_cat.category : category (functor_cat C D) := {
  id'     := id_trans,
  comp    := vcomp,
  id_comp := by
    intro F G
    intro { app := η, naturality := _ }
    apply nat_ext
    simp [id', id_trans, comp, vcomp]
  comp_id := by
    intro F G
    intro { app := η, naturality := _ }
    apply nat_ext
    simp [id', id_trans, comp, vcomp]
  assoc := by
    intro F G H K
    intro { app := f, naturality := _ }
    intro { app := g, naturality := _ }
    intro { app := h, naturality := _ }
    apply nat_ext
    simp [comp, vcomp]
}

end nat_trans

section hom_functor

variable {C : hom_struct} [category C]

-- I originally defined this inline inside the struct for the functor.
-- But that caused the proof goals to be huge.
def y_obj (c: C.obj) : (functor Cᵒᵖ set) := {
    obj := fun d => C.hom d c
    map := fun f g => g ∘ f -- f gets sent to precomposition with f
    map_id := by
      intros
      simp [id']
    map_comp := by
      intros
      simp [comp]
  }

def y_map {c d: C.obj} (f: C.hom c d) : nat_trans (y_obj c) (y_obj d) := {
  app := fun c g => f ∘ g
  naturality := by
    intros -- I guess it is more or less readable now.
    simp [y_obj, comp]
}

def y : functor C (functor_cat Cᵒᵖ set) := {
  obj := y_obj
  map := y_map
  map_id := by
    intros
    apply nat_ext -- Ahh the proof state is so readable now
    simp [y_map, id',id_trans]
  map_comp := by
    intros
    apply nat_ext
    simp [y_map, comp, vcomp]
}

-- Define the dual by opping! Maybe I need equivalences of categories here...
-- I will also need the Yoneda lemma to deal with universal properties.

-- theorem opop : C = (C.opposite)ᵒᵖ  := by
-- simp [hom_struct.opposite, obj, hom]

end hom_functor

end category_theory
