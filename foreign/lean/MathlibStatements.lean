import Lean

open Lean

namespace RainbowMathlibStatements

private def quoteString (value : String) : String := toString (repr value)

private partial def levelEDN : Level → String
  | .zero => "[:zero]"
  | .succ level => s!"[:succ {levelEDN level}]"
  | .max left right => s!"[:max {levelEDN left} {levelEDN right}]"
  | .imax left right => s!"[:imax {levelEDN left} {levelEDN right}]"
  | .param name => s!"[:param {quoteString name.toString}]"
  | .mvar id => s!"[:unsupported-level :mvar {quoteString (toString (repr id))}]"

private def binderEDN : BinderInfo → String
  | .default => ":explicit"
  | .implicit => ":implicit"
  | .strictImplicit => ":strict-implicit"
  | .instImplicit => ":instance-implicit"

private partial def writeExprEDN (handle : IO.FS.Stream) : Expr → IO Unit
  | .bvar index => handle.putStr s!"[:bound {index}]"
  | .sort level => handle.putStr s!"[:sort {levelEDN level}]"
  | .const name levels =>
      handle.putStr
        s!"[:const {quoteString name.toString} [{String.intercalate " " (levels.map levelEDN)}]]"
  | .app function argument => do
      handle.putStr "[:app "
      writeExprEDN handle function
      handle.putStr " "
      writeExprEDN handle argument
      handle.putStr "]"
  | .lam _ type body binder => do
      handle.putStr "[:lam "
      writeExprEDN handle type
      handle.putStr " "
      writeExprEDN handle body
      handle.putStr s!" {binderEDN binder}]"
  | .forallE _ type body binder => do
      handle.putStr "[:pi "
      writeExprEDN handle type
      handle.putStr " "
      writeExprEDN handle body
      handle.putStr s!" {binderEDN binder}]"
  | .letE _ type value body _ => do
      handle.putStr "[:let "
      writeExprEDN handle type
      handle.putStr " "
      writeExprEDN handle value
      handle.putStr " "
      writeExprEDN handle body
      handle.putStr "]"
  | .lit literal =>
      handle.putStr s!"[:unsupported :literal {quoteString (toString (repr literal))}]"
  | .mdata _ expression => writeExprEDN handle expression
  | .mvar id =>
      handle.putStr s!"[:unsupported :mvar {quoteString (toString (repr id))}]"
  | .fvar id =>
      handle.putStr s!"[:unsupported :fvar {quoteString (toString (repr id))}]"
  | .proj typeName index structExpr => do
      handle.putStr
        s!"[:unsupported :projection {quoteString typeName.toString} {index} "
      writeExprEDN handle structExpr
      handle.putStr "]"

private def parseManifestLine (line : String) : IO (String × System.FilePath) := do
  match line.splitOn "\t" with
  | [moduleName, path] => pure (moduleName, path)
  | _ => throw <| IO.userError s!"invalid module manifest line: {line}"

@[noinline] private def emitParts (handle : IO.FS.Stream)
    (requestedNames requestedLocations : Std.ExtHashSet String)
    (moduleName : String) (path : System.FilePath)
    (parts : Array (ModuleData × CompactedRegion)) :
    IO (Array CompactedRegion × Array String) := do
  let some (privateData, _) := parts[2]? |
    throw <| IO.userError s!"missing private olean part: {path}"
  let mut found := #[]
  for info in privateData.constants do
    let name := info.name.toString
    -- `name` may be backed by the compacted region. Return the matching key
    -- retained by the request set so completeness checks remain valid after
    -- `emitOlean` frees that region.
    if let some requestedName := requestedNames.get? name then
      if requestedLocations.contains name ||
          requestedLocations.contains (name ++ "|" ++ moduleName) then
        found := found.push requestedName
        let typeFingerprint := hash info.type
        let universes := info.levelParams.map (fun level => quoteString level.toString)
        handle.putStr <|
          "{:rainbow.catalog/kind :statement " ++
          s!":foreign/name {quoteString name} " ++
          s!":foreign/module {quoteString moduleName} " ++
          s!":foreign/universes [{String.intercalate " " universes}] " ++
          s!":foreign/type-fingerprint {quoteString s!"lean-hash64:{typeFingerprint}"} " ++
          ":foreign/type "
        writeExprEDN handle info.type
        handle.putStrLn " :foreign/value :redacted :foreign/location nil}"
  return (parts.map (·.2), found)

private unsafe def emitOlean (handle : IO.FS.Stream)
    (requestedNames requestedLocations : Std.ExtHashSet String) (moduleName : String)
    (path : System.FilePath) : IO (Array String) := do
  let (regions, found) ← emitParts handle requestedNames requestedLocations moduleName path
    (← readModuleDataParts
      #[path, path.addExtension "server", path.addExtension "private"])
  for region in regions do
    region.free
  return found

unsafe def run (arguments : List String) : IO UInt32 := do
  let [manifestPath, requestsPath] := arguments |
    throw <| IO.userError "usage: MathlibStatements MANIFEST.tsv REQUESTS.tsv"
  let requests ← IO.FS.readFile requestsPath
  let requestedLines := requests.splitOn "\n" |>.filter (fun value => !value.isEmpty)
  let requestedEntries ← requestedLines.mapM fun line =>
    match line.splitOn "\t" with
    | [name] => pure (name, name)
    | [name, moduleName] => pure (name, name ++ "|" ++ moduleName)
    | _ => throw <| IO.userError s!"invalid statement request: {line}"
  let requestedNamesArray := requestedEntries.map (·.1) |>.toArray
  let requestedNames : Std.ExtHashSet String :=
    requestedEntries.foldl (fun names entry => names.insert entry.1) {}
  let requestedLocations : Std.ExtHashSet String :=
    requestedEntries.foldl (fun locations entry => locations.insert entry.2) {}
  if requestedNames.size != requestedEntries.length then
    throw <| IO.userError "statement names must be distinct"
  let manifest ← IO.FS.readFile manifestPath
  let entries ← (manifest.splitOn "\n" |>.filter (fun line => !line.isEmpty)).mapM
    parseManifestLine
  let handle ← IO.getStdout
  handle.putStrLn <|
    "{:rainbow.catalog/kind :header :foreign/system :lean :foreign/library :mathlib " ++
    ":foreign/version \"v4.30.0\" " ++
    ":foreign/commit \"c5ea00351c28e24afc9f0f84379aa41082b1188f\" " ++
    ":foreign/proofs :redacted :foreign/selection :bounded " ++
    ":foreign/schema-version 1}"
  let mut found : Std.HashSet String := {}
  for (moduleName, path) in entries do
    for name in ← emitOlean handle requestedNames requestedLocations moduleName path do
      found := found.insert name
  if found.size != requestedNames.size then
    let missing := requestedNamesArray.filter (fun name => !found.contains name)
    throw <| IO.userError s!"requested statements not found: {missing}"
  handle.flush
  return 0

end RainbowMathlibStatements

unsafe def main (arguments : List String) : IO UInt32 :=
  RainbowMathlibStatements.run arguments
