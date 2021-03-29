
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

def test : MetaM Unit := do
  -- This is quite convenient to do typeclass inference:
  let t <- mkAppM `f #[mkNatLit 2]
  trace[Meta.debug]! "t: {t}"
  let t <- whnf t

-- `MetaM` is probably the right API to consume in order to build custom lean objects. Moreover, it is the right context to do stuff like type inference, normal forms, etc. It seems like it is nice and logical.
-- `TermElabM` seems to be fundamentally tied to the lean elaborator and its macro expansion mechanism, I don't want to have anything to do with that.

-- Hm, can we generate structs from `MetaM`? The structs seem to be stored in the environment.

set_option trace.Meta.debug true

#eval test
-- #print lambdaTelescope
-- #print mkLambdaFVars
-- #print (typeof! lambdaTelescope)