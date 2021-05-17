
import Lean
import ReadableLean.Grammar
import ReadableLean.Deserialize
import ReadableLean.Logic
import ReadableLean.Meaning


open Lean
open Meta
open ReadableLean
open DeserializationError

-- At some point later, in the CLI interface or sth:
def file [Monad m] [MonadLiftT IO m] : m String := IO.FS.readFile "paraLemma.json"

def json : DeserializeM Json := do
  let contents <- file
  -- How cool! `MonadLiftT` is automatically used!
  match Json.parse contents with
    | Except.ok json => json
    | Except.error msg => throw (parsingError msg)

def main (args : List String): IO Unit := do
  let chain <- json >>= Para.fromJson |>.run
  match chain with
    | Except.error e => panic! (toString e)
    | Except.ok p =>
      -- let a := foo
      -- We reimport `Predef` in order to have a more or less clean environment
      -- We might want to throw out more modules out of the env in order to remove
      -- unnecessary garbage.

      -- initSearchPath --(the `getBuiltinSearchPath` is wrong when running executables!)
      -- let sp ← addSearchPathFromEnv []
      -- Where are the native implementations?
      searchPathRef.set ["objects", "/nix/store/xn6b2h5izwi786gs5995fn0fcs7yif06-lean-stage1/lib/lean"]
      let sp <- searchPathRef.get
      IO.println sp

      -- let a <- findOLean `A
      -- IO.println ("olean: ".append a)

      IO.println "importing modules..."
      -- let env <- importModules [{module := `Init}, {module := `Prelude}, {module := `A}] Options.empty
      let env <- importModules [{module := `Prelude},{module := `A}] Options.empty
      IO.println "imported modules."
      IO.println env.allImportedModuleNames

      let op : MetaM Lean.Expr := do
        let x <- inferType (mkConst `point)
        p.interpret
        let ns <- resolveGlobalConstNoOverload `TransitivityOfCongruence
        inferType (mkConst ns)

      let (expr, _, _) <- op.toIO { openDecls := [OpenDecl.simple `Prelude []] } { env := env }
      IO.println (toString expr)

-- #eval main []

-- I should probably use the lean package `/nix/store/xn6b2h5izwi786gs5995fn0fcs7yif06-lean-stage1/lib/lean` for manually compiling `.olean` files.
