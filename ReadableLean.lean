
import Lean
import ReadableLean.Grammar
import ReadableLean.Deserialize
import ReadableLean.Logic
import ReadableLean.Meaning


open Lean
open Meta
open ReadableLean
open DeserializationError

-- DISCLAIMER: This code is just me experimenting around, if you want to see code that
-- is actually useful, you should look at the `ReadableLean` folder.

def fromFile (filename: String) : DeserializeM Para := do
  let contents <- IO.FS.readFile filename
  -- How cool! `MonadLiftT` is automatically used!
  match Json.parse contents with
    | Except.ok json => Para.fromJson json
    | Except.error msg => throw (parsingError msg)

def main (args : List String): IO Unit := do
  let p <- fromFile "paraLemma.json" |>.run
  match p with
    | Except.error e => panic! (toString e)
    | Except.ok p =>
      searchPathRef.set ["objects", "/nix/store/xn6b2h5izwi786gs5995fn0fcs7yif06-lean-stage1/lib/lean"]
      let sp <- searchPathRef.get
      let env <- importModules [{module := `Prelude}] Options.empty

      let op : MetaM Lean.Expr := do
        p.interpret
        let ns <- resolveGlobalConstNoOverload `TransitivityOfCongruence
        inferType (mkConst ns)

      let (expr, _, _) <- op.toIO { openDecls := [OpenDecl.simple `Prelude []] } { env := env }
      IO.println (toString expr)

-- #eval main []
