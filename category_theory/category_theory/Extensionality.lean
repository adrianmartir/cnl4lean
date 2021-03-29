
-- Lets prove an extensionality example.

structure Pointed (obj : Type v) (motive : obj -> Type u) where
  point : obj
  property : motive point--point = point


-- This is inspired by `PSigma.eta` in `Init/Core.lean`.
theorem ext {X: Type v} {motive : X -> Type u} {a b : X} {s : motive a} {t : motive b} (p: a = b) (q: (Eq.ndrec s p = t)) : Pointed.mk a s = Pointed.mk b t := by
  subst p
  subst q
  exact rfl