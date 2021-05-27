-- Some basic Category-theoretic constructions
namespace CategoryTheory


-- This notation is optimal, much better than what was in mathlib.
-- hom sets should always be anotated with the Category they are meant
-- to be taken on. Unlike identities and composition operators and axioms.
-- Otherwise it is very confusing when considering opposite categories.
structure HomStruct where
  obj : Type u
  hom : obj → obj → Type v


class Category (C : HomStruct) where
  id' : (c : C.obj) -> C.hom c c
  comp : {c d e : C.obj} -> C.hom c d -> C.hom d e -> C.hom c e
  id_comp : {c d : C.obj} -> (f : C.hom c d) -> ((comp (id' c) f) = f)
  comp_id : {c d : C.obj} -> (f : C.hom c d) -> ((comp f (id' d)) = f)
  assoc : {a b c d : C.obj} -> (f : C.hom a b) -> (g : C.hom b c) -> (h : C.hom c d)
      -> comp (comp f g) h = comp f (comp g h)

notation:80 lhs " ∘ " rhs:81  => Category.comp rhs lhs

open HomStruct
open Category

attribute [simp] Category.id_comp Category.comp_id Category.assoc


def HomStruct.opposite (C: HomStruct) : HomStruct := {
  obj := C.obj
  hom := fun f g => C.hom g f
}

notation:1030 arg "ᵒᵖ"  => HomStruct.opposite arg

instance Category.opposite (C: HomStruct) [Category C]: Category Cᵒᵖ := {
  id' := fun c => id' (C := C) c
  comp := fun f g => comp (C := C) g f
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

theorem opop (C: HomStruct) [Category C]: C = (C.opposite)ᵒᵖ  := by
  revert C
  intro { obj := obj, hom := hom}
  simp [HomStruct.opposite]

attribute [simp] opop

universe u

abbrev SmallCategory (C : HomStruct) := Category.{u,u} C
abbrev LargeCategory (C : HomStruct) := Category.{u+1,u} C


def Set : HomStruct := {
  obj := Type u,
  hom := fun a b => a -> b
}

instance Set.Category : LargeCategory Set :=
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

def inverses (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) (g: C.hom d c) := g ∘ f = id' c ∧ f ∘ g = id' d

theorem inverse_unique (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) (g h: C.hom d c) : inverses C f g ∧ inverses C f h -> g = h := by
  intro ⟨⟨_,p⟩,⟨q,_⟩⟩
  have r : (h ∘ f) ∘ g = h := by
    rw [<- assoc, p, id_comp]

  rw [<- r, q, comp_id]

def isomorphism (C: HomStruct) [Category C] {c d: C.obj} (f: C.hom c d) :=
  exists (g: C.hom d c), inverses C f g

structure Functor (C D: HomStruct) [Category C] [Category D] where
  obj : C.obj -> D.obj
  map : {c d : C.obj} -> C.hom c d -> D.hom (obj c) (obj d)
  map_id : {c : C.obj} -> map (id' c) = id' (obj c)
  map_comp : {c d e : C.obj} -> (f : C.hom c d) -> (g : C.hom d e) -> map (g ∘ f) = map g ∘ map f

attribute [simp] Functor.map_id Functor.map_comp


def fully_faithful {C D: HomStruct} [Category C] [Category D] (F: Functor C D) :=
  forall c d : C.obj, isomorphism Set (F.map (c := c) (d := d))

section NatTrans

variable {C : HomStruct} [Category C]
variable {D : HomStruct} [Category D]

structure NatTrans (F G : Functor C D) :=
  app : (c : C.obj) -> D.hom (F.obj c) (G.obj c)
  naturality : {c d : C.obj} -> (f : C.hom c d) -> app d ∘ (F.map f) = (G.map f) ∘ app c

def FunctorCat (C: HomStruct) [Category C] (D: HomStruct) [Category D]: HomStruct := {
  obj := Functor C D
  hom := NatTrans
}

open NatTrans

def idTrans (F : Functor C D) : NatTrans F F := {
  app := fun c => id' (Functor.obj F c),
  naturality := by
    intro c d f
    simp
}

def vComp {F G H : Functor C D} (η : NatTrans F G) (μ : NatTrans G H) : NatTrans F H := {
  app := fun c => (app μ c) ∘ (app η c),
  naturality := by
    intro c d f
    simp
    rw [<- naturality μ f]
    rw [<- Category.assoc]
    rw [naturality η f]
    rw [Category.assoc]
}

theorem nat_ext {F G : Functor C D} : (η μ : NatTrans F G) ->(p: η.app = μ.app) -> (η = μ) := by
  intro { app := η, naturality := _ }
  intro { app := μ, naturality := _ }
  intro p
  subst p
  simp

instance : Category (FunctorCat C D) := {
  id'     := idTrans,
  comp    := vComp,
  id_comp := by
    intro F G
    intro { app := η, naturality := _ }
    apply nat_ext
    simp [id', idTrans, comp, vComp]
  comp_id := by
    intro F G
    intro { app := η, naturality := _ }
    apply nat_ext
    simp [id', idTrans, comp, vComp]
  assoc := by
    intro F G H K
    intro { app := f, naturality := _ }
    intro { app := g, naturality := _ }
    intro { app := h, naturality := _ }
    apply nat_ext
    simp [comp, vComp]
}

end NatTrans

section Yoneda



def yObj (c: C.obj) : (Functor Cᵒᵖ Set) := {
    obj := fun d => C.hom d c
    -- f gets sent to precomposition with f
    map := fun f g => g ∘ f
    map_id := by
      intros
      simp [id']
    map_comp := by
      intros
      simp [comp]
  }

-- notation "Hom(-," arg ")"  => yObj arg

def yMap {c d: C.obj} (f: C.hom c d) : NatTrans (yObj c) (yObj d) := {
  app := fun c g => f ∘ g
  naturality := by
    intros
    simp [yObj, comp]
}

def y : Functor C (FunctorCat Cᵒᵖ Set) := {
  obj := yObj
  map := yMap
  map_id := by
    intros
    apply nat_ext
    simp [yMap, id', idTrans]
  map_comp := by
    intros
    apply nat_ext
    simp [yMap, comp, vComp]
}

-- At this point I should talk about representability and give a few examples - It should be emphazised how important that concept is

def yonedaMap (c : C.obj) (F: Functor Cᵒᵖ Set) (η: NatTrans (y.obj c) F) : F.obj c := η.app c (id' c)

def yonedaMapInv (c : C.obj) (F: Functor Cᵒᵖ Set) (x: F.obj c) : NatTrans (y.obj c) F := {
  app := fun d f => F.map f x
  naturality := by
    intros d e f
    simp [y, yObj, comp]
    apply funext
    intros h
    -- It honestly is a bit confusing not knowing in which category
    -- the composition takes place
    have p: comp (C := C) f h = comp (C := Cᵒᵖ) h f  := Eq.refl _
    rw [p, Functor.map_comp]
    simp [comp]
}

theorem yoneda (c : C.obj) (F: Functor Cᵒᵖ Set) : inverses Set (yonedaMap c F) (yonedaMapInv c F) := ⟨
  by
    simp [yonedaMap, yonedaMapInv]
    apply funext
    intro { app := η, naturality := nat }
    simp [comp,id',y,yObj]
    apply funext
    intros d
    apply funext
    intros f
    -- Rewrite the application in the goal as a composition in order
    -- to apply naturality
    have p: F.map f (η c (id' c)) = (comp (η c) (F.map f)) (id' c) := Eq.refl _
    rw [p, <- nat f]
    simp [y, yObj, comp],
  by
    simp [yonedaMap, yonedaMapInv,comp]
    apply funext
    intro x
    have p: id' (C := C) c = id' (C := Cᵒᵖ) c  := Eq.refl _
    rw [p, Functor.map_id]
⟩

#print yMap
#print yoneda

theorem y_fully_faithful: fully_faithful (y (C := C)) := by
  simp [fully_faithful]
  intros c d
  have inv: (FunctorCat Cᵒᵖ Set).hom (y.obj c) (y.obj d) -> C.hom c d := yonedaMap c (y.obj d)
  -- exact ⟨ inv, by
  --   apply yoneda
  -- ⟩
  have p := yoneda c (y.obj d)



-- Redo part of Riehl's universal properties chapter as an 'application' of the Yoneda lemma.
-- Motto: The functor category has many good properties, and we can use it to characterize arrows into a fictional object. Then we can decide whether it exists.

end Yoneda

-- We can start limits and colimits here..

end CategoryTheory
