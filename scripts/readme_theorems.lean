import NormalityChecker
import Lean

/-! Regenerate the declaration directory from the compiled library.

Two artifacts are produced and checked:

* the collapsible module directory between the markers in `README.md`;
* the machine-readable manifest `docs/data/declarations.json`, one JSON object per
  named public theorem or lemma, with its fully qualified name, module, file,
  source lines, keyword and docstring.

Declaration ranges give the identifier's actual source line. Structure projections
and generated equations are not independently stated theorems. Run after
`lake build` from the repository root. With `NORMALITY_UPDATE_THEOREM_INDEX=1` the
script rewrites stale artifacts and then regenerates the Markdown pages derived from
the manifest (`python3 scripts/portal.py build`). Otherwise it fails on any
difference. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut sources : Std.HashMap Name (Array String) := {}
  let mut entries : Array (String × Nat × String × Json) := #[]
  for (name, info) in env.constants.toList do
    let .thmInfo _ := info | continue
    if isPrivateName name || name.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless `NormalityChecker |>.isPrefixOf mod do continue
    let some loc ← findDeclarationRanges? name | continue
    let path := mod.toString.replace "." "/" ++ ".lean"
    unless sources.contains mod do
      sources := sources.insert mod ((← IO.FS.readFile path).splitOn "\n").toArray
    let lines := sources[mod]!
    let line := loc.selectionRange.pos.line
    -- Include the preceding line too, for declarations with the name on a new line.
    let before := (lines[line-1]!.take loc.selectionRange.pos.column).toString
    let command := ((if line > 1 then lines[line-2]! ++ "\n" else "") ++ before).trimAsciiEnd
    let kind := if command.endsWith "theorem" then "theorem"
      else if command.endsWith "lemma" then "lemma" else ""
    if kind.isEmpty then continue
    let label := name.getString!
    let doc := ((← findDocString? env name).getD "").trimAscii.toString
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("label", toJson label),
      ("module", toJson mod.toString),
      ("file", toJson path),
      ("line", toJson line),
      ("endLine", toJson loc.range.endPos.line),
      ("kind", toJson kind),
      ("doc", toJson doc)]
    entries := entries.push (path, line, label, record)
  entries := entries.qsort (fun a b => if a.1 == b.1 then a.2.1 < b.2.1 else a.1 < b.1)
  let mut previous := ""
  let mut directory := s!"<details>\n<summary>Browse all {entries.size} public theorems and lemmas by Lean module</summary>\n"
  for (path, line, label, _) in entries do
    if path != previous then
      let title := (path.dropPrefix "NormalityChecker/").dropSuffix ".lean"
      directory := directory ++ s!"\n- **{title}** · "
      previous := path
    else
      directory := directory ++ " · "
    directory := directory ++ s!"[{label}]({path}#L{line})"
  directory := directory ++ "\n\n</details>"
  let manifest := "[\n" ++ ",\n".intercalate (entries.toList.map (·.2.2.2.compress)) ++ "\n]\n"
  let update := (← IO.getEnv "NORMALITY_UPDATE_THEOREM_INDEX") == some "1"
  let stale := "Run NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean"
  let text ← IO.FS.readFile "README.md"
  let start := "<!-- BEGIN LEAN THEOREM INDEX -->\n"
  let stop := "\n<!-- END LEAN THEOREM INDEX -->"
  let [intro, tail] := text.splitOn start | throwError "Expected one start marker for the README theorem index"
  let [old, rest] := tail.splitOn stop | throwError "Expected one end marker for the README theorem index"
  let manifestPath : System.FilePath := "docs/data/declarations.json"
  let oldManifest ← if ← manifestPath.pathExists then IO.FS.readFile manifestPath else pure ""
  let mut changed := false
  if old != directory then
    unless update do throwError s!"README theorem links are stale. {stale}"
    IO.FS.writeFile "README.md" (intro ++ start ++ directory ++ stop ++ rest)
    changed := true
  if oldManifest != manifest then
    unless update do throwError s!"The declaration manifest {manifestPath} is stale. {stale}"
    IO.FS.createDirAll "docs/data"
    IO.FS.writeFile manifestPath manifest
    changed := true
  if update then
    let out ← IO.Process.output { cmd := "python3", args := #["-B", "scripts/portal.py", "build"] }
    unless out.exitCode == 0 do
      throwError s!"Derived documentation failed to build:\n{out.stdout}{out.stderr}"
  logInfo m!"README index and manifest verified against {entries.size} named public theorems and lemmas{if changed then " (updated)" else ""}."
