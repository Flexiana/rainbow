import Lean

open Lean

namespace RainbowMathlibOleanCatalog

private def quoteString (value : String) : String := toString (repr value)

private structure TypeProfile where
  nodes : Nat := 0
  strictImplicit : Bool := false
  instanceImplicit : Bool := false
  literal : Bool := false
  metavariable : Bool := false
  freeVariable : Bool := false
  projection : Bool := false
  levelMetavariable : Bool := false
  deriving Inhabited

private def TypeProfile.merge (left right : TypeProfile) : TypeProfile :=
  { nodes := left.nodes + right.nodes
    strictImplicit := left.strictImplicit || right.strictImplicit
    instanceImplicit := left.instanceImplicit || right.instanceImplicit
    literal := left.literal || right.literal
    metavariable := left.metavariable || right.metavariable
    freeVariable := left.freeVariable || right.freeVariable
    projection := left.projection || right.projection
    levelMetavariable := left.levelMetavariable || right.levelMetavariable }

private def oneNode : TypeProfile := { nodes := 1 }

private def withBinder (profile : TypeProfile) : BinderInfo → TypeProfile
  | .strictImplicit => { profile with strictImplicit := true }
  | .instImplicit => { profile with instanceImplicit := true }
  | _ => profile

private partial def levelProfile : Level → TypeProfile
  | .zero | .param _ => oneNode
  | .succ level => oneNode.merge (levelProfile level)
  | .max left right | .imax left right =>
      (oneNode.merge (levelProfile left)).merge (levelProfile right)
  | .mvar _ => { oneNode with levelMetavariable := true }

private partial def exprProfileM (expression : Expr) :
    StateM (Std.HashSet Expr) TypeProfile := do
  let seen ← get
  if seen.contains expression then
    return {}
  set (seen.insert expression)
  match expression with
  | .bvar _ => return oneNode
  | .sort level => return oneNode.merge (levelProfile level)
  | .const _ levels =>
      return levels.foldl
        (fun profile level => profile.merge (levelProfile level)) oneNode
  | .app function argument =>
      let functionProfile ← exprProfileM function
      let argumentProfile ← exprProfileM argument
      return (oneNode.merge functionProfile).merge argumentProfile
  | .lam _ type body binder | .forallE _ type body binder =>
      let typeProfile ← exprProfileM type
      let bodyProfile ← exprProfileM body
      return withBinder ((oneNode.merge typeProfile).merge bodyProfile) binder
  | .letE _ type value body _ =>
      let typeProfile ← exprProfileM type
      let valueProfile ← exprProfileM value
      let bodyProfile ← exprProfileM body
      return ((oneNode.merge typeProfile).merge valueProfile).merge bodyProfile
  | .lit _ => return { oneNode with literal := true }
  | .mdata _ inner =>
      return oneNode.merge (← exprProfileM inner)
  | .mvar _ => return { oneNode with metavariable := true }
  | .fvar _ => return { oneNode with freeVariable := true }
  | .proj _ _ structExpr =>
      return { oneNode.merge (← exprProfileM structExpr) with projection := true }

private def exprProfile (expression : Expr) : TypeProfile :=
  (exprProfileM expression {}).1

private def profileEDN (profile : TypeProfile) : String :=
  "{" ++ s!":nodes {profile.nodes} " ++
  s!":strict-implicit? {profile.strictImplicit} " ++
  s!":instance-implicit? {profile.instanceImplicit} " ++
  s!":literal? {profile.literal} :metavariable? {profile.metavariable} " ++
  s!":free-variable? {profile.freeVariable} :projection? {profile.projection} " ++
  s!":level-metavariable? {profile.levelMetavariable}" ++ "}"

private def kindEDN : ConstantInfo → String
  | .axiomInfo _ => ":axiom"
  | .thmInfo _ => ":theorem"
  | .defnInfo _ => ":definition"
  | .opaqueInfo _ => ":opaque"
  | .quotInfo _ => ":quotient"
  | .inductInfo _ => ":inductive"
  | .ctorInfo _ => ":constructor"
  | .recInfo _ => ":recursor"

private def parseManifestLine (line : String) : IO (String × System.FilePath) := do
  match line.splitOn "\t" with
  | [moduleName, path] => pure (moduleName, path)
  | _ => throw <| IO.userError s!"invalid module manifest line: {line}"

private def emitModule (handle : IO.FS.Stream) (moduleName : String)
    (publicNames : Std.HashSet Name) (data : ModuleData) : IO Unit := do
  for info in data.constants do
    let levels := info.levelParams.map (fun level => quoteString level.toString)
    let profile := exprProfile info.type
    handle.putStrLn <|
      "{:rainbow.catalog/kind :declaration " ++
      s!":foreign/name {quoteString info.name.toString} :foreign/kind {kindEDN info} " ++
      s!":foreign/module {quoteString moduleName} " ++
      s!":foreign/universes [{String.intercalate " " levels}] " ++
      s!":foreign/type-fingerprint {quoteString s!"lean-hash64:{hash info.type}"} " ++
      s!":foreign/type-profile {profileEDN profile} :foreign/value :redacted " ++
      s!":foreign/unsafe? {if info.isUnsafe then "true" else "false"} " ++
      s!":foreign/public? {if publicNames.contains info.name then "true" else "false"} " ++
      ":foreign/location nil}"

@[noinline] private def emitParts (handle : IO.FS.Stream) (moduleName : String)
    (path : System.FilePath)
    (parts : Array (ModuleData × CompactedRegion)) : IO (Array CompactedRegion) := do
  let some (publicData, _) := parts[0]? |
    throw <| IO.userError s!"missing public olean part: {path}"
  let some (privateData, _) := parts[2]? |
    throw <| IO.userError s!"missing private olean part: {path}"
  let publicNames := publicData.constNames.foldl (fun names name => names.insert name) {}
  emitModule handle moduleName publicNames privateData
  return parts.map (·.2)

private unsafe def emitOlean (handle : IO.FS.Stream) (moduleName : String)
    (path : System.FilePath) : IO Unit := do
  let regions ← emitParts handle moduleName path (← readModuleDataParts
    #[path, path.addExtension "server", path.addExtension "private"])
  for region in regions do
    region.free

unsafe def run (arguments : List String) : IO UInt32 := do
  let (manifestPath, writeHeader) ← match arguments with
    | [path] => pure (path, true)
    | [path, "--no-header"] => pure (path, false)
    | _ => throw (IO.userError
      "usage: MathlibOleanCatalog MANIFEST.tsv [--no-header]")
  let manifest ← IO.FS.readFile manifestPath
  let entries ← (manifest.splitOn "\n" |>.filter (fun line => !line.isEmpty)).mapM
    parseManifestLine
  let handle ← IO.getStdout
  if writeHeader then
    handle.putStrLn <|
      "{:rainbow.catalog/kind :header :foreign/system :lean :foreign/library :mathlib " ++
      ":foreign/version \"v4.30.0\" " ++
      ":foreign/commit \"c5ea00351c28e24afc9f0f84379aa41082b1188f\" " ++
      ":foreign/proofs :redacted " ++
      ":foreign/statement-representation :lean-hash64-profile " ++
      ":foreign/schema-version 2}"
  for (moduleName, path) in entries do
    emitOlean handle moduleName path
  handle.flush
  return 0

end RainbowMathlibOleanCatalog

unsafe def main (arguments : List String) : IO UInt32 :=
  RainbowMathlibOleanCatalog.run arguments
