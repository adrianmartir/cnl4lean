
import Lean
import CNL4Lean.Grammar
import CNL4Lean.Deserialize
import CNL4Lean.Logic
import CNL4Lean.Meaning
import CNL4Lean.Predef


open Lean
open Meta
open CNL4Lean
open DeserializationError

-- At some point later, in the CLI interface or sth:
def file [Monad m] [MonadLiftT IO m] : m String := IO.FS.readFile "paraLemma.json"

def json : DeserializeM Json := do
  let contents <- file
  -- How cool! `MonadLiftT` is automatically used!
  match Json.parse contents with
    | Except.ok json => json
    | Except.error msg => throw (parsingError msg)

def main' : IO Expr := do
  let chain <- json >>= Para.get |>.run
  match chain with
    | Except.error e => panic! (toString e)
    | Except.ok (Grammar.Para.lemma' _ lemma) =>
      -- We reimport `Predef` in order to have a more or less clean environment
      -- We might want to throw out more modules out of the env in order to remove
      -- unnecessary garbage.
      -- We might want to manually compile `Predef` to an `.olean` file in the future.
      let env <- importModules [{module := `CNL4Lean.Predef}] Options.empty
      let lemma : MetaM Expr := Means.interpret lemma
      let (expr, _, _) <- lemma.toIO { openDecls := [OpenDecl.simple `CNL4Lean.Predef []] } { env := env }

      expr
    | _ => panic! "The world is going to explode!!"


-- #eval main'
