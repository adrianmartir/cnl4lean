
-- This file contains the builtin lean constants.
-- Somehow disable prelude when reading this?

def notPred (p: α -> Prop) (x: α): Prop := Not (p x)

def andPred (p1 : α -> Prop) (p2 : α -> Prop) (x: α) := And (p1 x) (p2 x)

def orPred (p1 : α -> Prop) (p2 : α -> Prop) (x: α) := Or (p1 x) (p2 x)

def truePred (x: α) := True

-- We can put the pattern -> lean translations here for now.
-- Maybe later I have a better idea.
