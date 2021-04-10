
import Lean

open Lean
open Meta

#eval "Hello, world!"

-- These are defined in `Lean/Environment.lean`
#check Environment
#check Environment.header
#check Environment.add

-- Interestingly
def defaultEnvironment : Environment := arbitrary

#eval defaultEnvironment.header.moduleNames
-- This seems to be the key to creating new environments!
-- I will use this when processing `.lean.tex` files!
#check importModules


-- These are defined in `Lean/Declaration.lean`
-- I will need these for constructing the stuff that I will add to my environment with `Lean.Environment.add`. Since `Lean.ConstantInfo` is essentially a coproduct of axiom, definition,...

#check mkAxiomValEx
#check mkDefinitionValEx
#check TheoremVal.mk

#check ConstantVal.mk
-- Note that these are not yet the kinds of objects that can be sent to the kernel. Instead, one needs to use `Lean.Declaration

-- Now lets look at `Lean.Expr`

#check mkApp
#check mkForall
#check mkLambda
#check BinderInfo

-- Note: in `Expr`, for the kernel the metadata and the metavariables are fully irrelevant!! Perhaps some of the implementation details of combining `.lean.tex` and `.tex` formats should be implemented using metadata?


-- Hmmm, do we have json support?

#eval Json.parse "{ \"key\": \"value\"}"

-- Uhhh this is quite nice, the relevant defintions are in
-- `Lean/Data/Json/`

-- Probably the most important and essential part is the CNL elaboration to a `.olean` file.

-- Question: Why is the local context immutable in MetaM?

def f {α} [Add α] (x:α) : List α := [x,x,x+x]


set_option trace.Meta.debug true

variable (x : Int)

def test : MetaM Unit := do
  -- This does typeclass resolutions and resolves implicit parameters
  -- The informatin about `f` will be queried from the environment. The environment
  -- will probably be passed to the the `MetaM` monad when we call `#eval`. This also
  -- explains why the local context is empty.
  let t <- mkAppM `f #[mkNatLit 2]
  let s <- getConstInfo `f

  trace[Meta.debug] "t: {t}"
  trace[Meta.debug] "s: {s.type}"
  let t <- whnf t
  let type <- inferType t

  trace[Meta.debug] "type: {type}"
  let lc <- getLCtx
  let mc <- getMCtx

  -- Application is easy. Can we make a lambda abstraction? That would be interesting.
  trace[Meta.debug] "lc: {lc.getFVarIds}"

-- `MetaM` is probably the right API to consume in order to build custom lean objects. Moreover, it is the right context to do stuff like type inference, normal forms, etc. It seems like it is nice and logical.
-- `TermElabM` seems to be fundamentally tied to the lean elaborator and its macro expansion mechanism, I don't want to have anything to do with that.

-- Hm, can we generate structs from `MetaM`? The structs seem to be stored in the environment.
#eval test

#check isDefEq

-- For creating lambdas these functions are crucial. They call the `MetaM` monad with
-- the correct context!!
-- In the `Meta/Basic.lean` file there also seem to be telescopes for let bindings.
-- The `n` monad is a variable that is an actual `MetaM`
-- I will probably need to look for another function for actually creating lambdas,
-- since this one is just for traversing them.
-- Note that this also has to update the instance cache if there are instances in the
-- parameters of the lambda.
#print forallTelescope
#print lambdaTelescope

#print mkLambdaFVars


-- How to create a new free variable declaration (this intel has been extracted from
-- the how `lambdaTelescope` works).
-- let fvarId ← mkFreshId
-- let lctx := lctx.mkLocalDecl fvarId name type binderInfo

-- Then we can run a new `MetaM` monad in the correct context by using
#print withReader

-- I guess the only question left is how to correctly format names. The docstring of
-- `lctx.mkLocalDecl` from the `LocalContext.lean` file says that its API is very low 
-- level and that instead one should use `TacticM` or `TermElabM`. Since `MetaM` also
-- has a `mkFreshId` function(implements the corresponding typeclass), it should be
-- also safe to use `MetaM`

-- But I should look at `TermElabM` at least in order to get an idea about how
-- namespacing is supposed to work.
#print Elab.TermElabM


-- It seems like `CoreM` already has a `namespace` in its context. It also carries
-- around a list of open declarations.

-- #print (typeof! lambdaTelescope)