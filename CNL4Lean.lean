
import Lean
import CNL4Lean.Grammar
import CNL4Lean.Deserialize
import CNL4Lean.AppBuilder


open Lean
open CNL4Lean
open Deserializable
open DeserializationError

-- At some point later, in the CLI interface or sth:
def file [Monad m] [MonadLiftT IO m] : m String := IO.FS.readFile "paraDefn.json"

def json : DeserializeM Json := do
  let contents <- file
  -- How cool! `MonadLiftT` is automatically used!
  match Json.parse contents with
    | Except.ok json => json
    | Except.error msg => throw (parsingError msg)

def getPara : DeserializeM Grammar.Para := json >>= deserialize
-- This should simply be lowered to IO and then run.

def f : IO DeserializationError := do
  let chain <- getPara.run
  match chain with
    | Except.ok c => panic! "oh yes"
    | Except.error e => e


-- #eval f
