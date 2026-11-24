import NormalityChecker
import Lean

/-! Regenerate the README directory from the compiled library. Declaration ranges give
the identifier's actual source line. Structure projections and generated equations
are not independently stated theorems. Run after `lake build` from the repository root. -/

open Lean in
run_cmd do
  let env ← getEnv
  let mut sources : Std.HashMap Name (Array String) := {}
  let mut entries : Array (String × Nat × String) := #[]
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
    unless command.endsWith "theorem" || command.endsWith "lemma" do continue
    let label := name.getString!
    entries := entries.push (path, line, label)
  entries := entries.qsort (fun a b => if a.1 == b.1 then a.2.1 < b.2.1 else a.1 < b.1)
  let mut previous := ""
  let mut directory := s!"<details>\n<summary>Browse all {entries.size} public theorems and lemmas by Lean module</summary>\n"
  for (path, line, label) in entries do
    if path != previous then
      let title := (path.dropPrefix "NormalityChecker/").dropSuffix ".lean"
      directory := directory ++ s!"\n- **{title}** · "
      previous := path
    else
      directory := directory ++ " · "
    directory := directory ++ s!"[{label}]({path}#L{line})"
  directory := directory ++ "\n\n</details>"
  let text ← IO.FS.readFile "README.md"
  let start := "<!-- BEGIN LEAN THEOREM INDEX -->\n"
  let stop := "\n<!-- END LEAN THEOREM INDEX -->"
  let [intro, tail] := text.splitOn start | throwError "Expected one start marker for the README theorem index"
  let [old, rest] := tail.splitOn stop | throwError "Expected one end marker for the README theorem index"
  if old != directory then
    if (← IO.getEnv "NORMALITY_UPDATE_THEOREM_INDEX") == some "1" then
      IO.FS.writeFile "README.md" (intro ++ start ++ directory ++ stop ++ rest)
    else
      throwError "README theorem links are stale. Run NORMALITY_UPDATE_THEOREM_INDEX=1 lake env lean scripts/readme_theorems.lean"
  logInfo m!"README index verified against {entries.size} named public theorems and lemmas."
