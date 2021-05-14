
namespace ReadableLean.Predef
-- This file contains the builtin lean constants.
-- Somehow disable prelude when reading this?

def xor (p1: Prop) (p2: Prop) : Prop :=
  Or (And p1 (Not p2))
    (And (Not p1) p2)

def nor (p1: Prop) (p2: Prop) : Prop :=
  Not (Or p1 p2)

-- We can put the pattern -> lean translations here for now.
-- Maybe later I have a better idea.

constant Point : Type

def point (x: Point) : Prop := True

constant CongPred (x y z w: Point) : Prop
