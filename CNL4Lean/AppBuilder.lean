
import Lean

open Lean
open Lean.Meta


-- This code has been copied from `Lean/Meta/AppBuilder.lean`, but it has been modified such that it is allowed to modify the metavariable context. Honestly, I am not so sure I really understand what it does.
private def throwAppBuilderException {α} (op : Name) (msg : MessageData) : MetaM α :=
  throwError "AppBuilder for '{op}', {msg}"

private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← getMVarDecl mvarId
    let mvarVal  ← synthInstance mvarDecl.type
    assignExprMVar mvarId mvarVal
  let result ← instantiateMVars (mkAppN f args)
  -- if (← hasAssignableMVar result) then throwAppBuilderException methodName ("result contains metavariables" ++ indentExpr result)
  return result

private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
    if i >= xs.size then
      mkAppMFinal `mkAppM f args instMVars
    else match type with
      | Expr.forallE n d b c =>
        let d  := d.instantiateRevRange j args.size args
        match c.binderInfo with
        | BinderInfo.implicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | BinderInfo.instImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          loop b i j (args.push mvar) (instMVars.push mvar.mvarId!)
        | _ =>
          let x := xs[i]
          let xType ← inferType x
          if (← isDefEq d xType) then
            loop b (i+1) j (args.push x) instMVars
          else
            throwAppTypeMismatch (mkAppN f args) x
      | type =>
        let type := type.instantiateRevRange j args.size args
        let type ← whnfD type
        if type.isForall then
          loop type i args.size args instMVars
        else
          throwAppBuilderException `mkAppM m!"too many explicit arguments provided to{indentExpr f}\narguments{indentD xs}"
  loop fType 0 0 #[] #[]

private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType := cinfo.instantiateTypeLevelParams us
  return (f, fType)

/--
  Return the application `constName xs`.
  It tries to fill the implicit arguments before the last element in `xs`.

  Remark:
  ``mkAppM `arbitrary #[α]`` returns `@arbitrary.{u} α` without synthesizing
  the implicit argument occurring after `α`.
  Given a `x : (([Decidable p] → Bool) × Nat`, ``mkAppM `Prod.fst #[x]`` returns `@Prod.fst ([Decidable p] → Bool) Nat x`
-/
def mkAppM' (constName : Name) (xs : Array Expr) : MetaM Expr := do
  -- traceCtx `Meta.appBuilder <| withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    let r ← mkAppMArgs f fType xs
    trace[Meta.appBuilder] "constName: {constName}, xs: {xs}, result: {r}"
    return r


-- OLD CODE:
-- Simple unifying application.
-- * Doesn't deal with different argument types
-- * No coercions
-- * No propagating expected type for smarter coercions
-- * No synthetic metavariables
-- The lean application implementation is in `Elab/App.lean` and it has
-- **a lot** more features.
def app (f: Expr) (arg: Expr) : MetaM Expr := do
  let fType <- inferType f
  let dom <- fType.bindingDomain!
  let type <- inferType arg
  unless <- isDefEq dom type do throwError "Expected type {dom}, got {type}"
  mkApp f arg

-- -- Copied from `AppBuilder.lean`. Instantiates universe parameters.
-- private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
--   let cinfo ← getConstInfo constName
--   let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
--   let f := mkConst constName us
--   let fType := cinfo.instantiateTypeLevelParams us
--   return (f, fType)

-- private def appN (ident: Name) (args: Array Expr) : MetaM Expr := do
--   args.foldlM (fun f arg => app f arg) ((<- mkFun ident) |>.1)
