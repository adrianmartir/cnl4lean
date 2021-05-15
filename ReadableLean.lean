
-- import Lean
-- import ReadableLean.Grammar
-- import ReadableLean.Deserialize
-- import ReadableLean.Logic
-- import ReadableLean.Meaning
-- import ReadableLean.Predef


-- open Lean
-- open Meta
-- open ReadableLean
-- open DeserializationError

-- -- At some point later, in the CLI interface or sth:
-- def file [Monad m] [MonadLiftT IO m] : m String := IO.FS.readFile "paraLemma.json"

-- def json : DeserializeM Json := do
--   let contents <- file
--   -- How cool! `MonadLiftT` is automatically used!
--   match Json.parse contents with
--     | Except.ok json => json
--     | Except.error msg => throw (parsingError msg)

-- def main : IO Unit := do
--   let chain <- json >>= Para.fromJson |>.run
--   match chain with
--     | Except.error e => panic! (toString e)
--     | Except.ok p =>
--       -- We reimport `Predef` in order to have a more or less clean environment
--       -- We might want to throw out more modules out of the env in order to remove
--       -- unnecessary garbage.
--       -- We might want to manually compile `Predef` to an `.olean` file in the future.
--       let env <- importModules [{module := `ReadableLean.Predef}, {module := `A}] Options.empty

--       let op : MetaM Lean.Expr := do
--         p.interpret
--         let ns <- resolveGlobalConstNoOverload `TransitivityOfCongruence
--         inferType (mkConst ns)

--       let (expr, _, _) <- op.toIO { openDecls := [OpenDecl.simple `ReadableLean.Predef []] } { env := env }
--       IO.println "{expr}"

def main : IO Unit :=
  IO.println "Hello world!"
