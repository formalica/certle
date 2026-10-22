/-
Copyright (c) 2026 The mathlib4-sig Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Elab.Frontend
import Lean.Elab.Import
import Lean.Server.Utils
import Lean.Util.Path

/-!
# Replace theorem/lemma proofs in place, keeping definitional (`rfl`) and `simps` proofs (v5)

Same logic as v4, but **skips** theorems or lemmas declared with the `simps` attribute
(`@[simps]`, `@[simps!]`, etc.).  Keeping the original constructor proof of `simps`
declarations avoids the `Invalid 'simps' attribute. The body is not a constructor application`
error (such as on `affine_combination` in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`).

Usage:
```
lake env lean --run CertleExe.lean Mathlib/Data/Vector/Basic.lean
```

Passing zero files, or more than one file, is an error (exit code 1).
Loading and elaborating a single file at a time keeps imports, environments,
and initializer state predictable: one process, one file, one result line.

Equation-style declarations (`| pat => body`) are replaced with a single
wildcard arm `| _ => sorry`.  This works uniformly whether the declaration
originally has one arm (such as `mmap_cons` in `Mathlib/Data/Vector/Basic.lean`)
or many arms (such as `map_add_zsmul` in `Mathlib/Algebra/AddConstMap/Basic.lean`),
eliminating complex pattern matching while correctly terminating layout-sensitive
`do` blocks in signatures.

Declarations using `where` (such as `toCompleteDistribLattice` in
`Mathlib/Order/CompleteBooleanAlgebra.lean` or `span_singleton_eq_one_iff` in
`Mathlib/Algebra/Algebra/Operations.lean`) are replaced whole with ` := by sorry`.

v5 **fails loudly** (non-zero exit code) instead of silently reporting
`replaced 0 proof(s)` when

* the file's imports cannot be loaded (e.g. a missing `.olean`): without the
  imported notation (`f '' s`, `IsLUB ..`, `α ≃o β`, ...) the statements do
  not parse, every theorem loses its proof-body node, and nothing could be
  replaced (`Mathlib/Order/Bounds/OrderIso.lean` was silently skipped this
  way); or
* a `theorem`/`lemma` parses without a proof body at all, which indicates
  parse damage in the file.

Regression tests live in `CertleTest/` (`CertleTest/run.sh`).  They run the
executable against fixtures in a scratch Lake project under `/tmp/certle-test`,
which is the only place that depends on Mathlib; `certle` itself does not.
-/

open Lean Elab Meta

namespace ReplaceTheoremProofsRflV5

/-- The text that replaces a non-reflexive `declValSimple` right-hand side. -/
def defaultBody : String := " := by sorry"

/-- The text that replaces an equation declaration's arms (one wildcard arm). -/
def eqnArmBody : String := "| _ => sorry"

/-- Node kinds that form the right-hand side of a declaration. -/
def isTheoremRhsNode (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.declValSimple ||
  stx.isOfKind ``Parser.Command.declValEqns ||
  stx.isOfKind ``Parser.Command.whereStructInst

/--
In Mathlib, `lemma` is a (higher-priority) command of its own whose syntax name is the
unqualified `lemma`; standalone Batteries users instead get `Batteries.Tactic.Lemma.lemmaCmd`.
We recognise both.
-/
def lemmaKinds : List Name :=
  ["lemma".toName, "Batteries.Tactic.Lemma.lemmaCmd".toName]

/-- Is `stx` a `lemma` command of either origin? -/
def isLemmaNode (stx : Syntax) : Bool :=
  lemmaKinds.any stx.isOfKind

/-- Commands that only wrap other commands and must be descended into. -/
def isCommandWrapper (stx : Syntax) : Bool :=
  stx.isOfKind ``Parser.Command.mutual ||
  stx.isOfKind ``Parser.Command.in ||
  stx.isOfKind ``Parser.Command.withWeakNamespace ||
  stx.isOfKind ``Parser.Command.withExporting

/--
Skip a (possibly nested) block comment.  `cs` is the character list *after* the
opening delimiter.  Returns the remaining characters, and whether the comment was
properly closed.
-/
partial def skipBlockComment (cs : List Char) (depth : Nat) : List Char × Bool :=
  match cs with
  | '-' :: '/' :: rest => if depth == 1 then (rest, true) else skipBlockComment rest (depth - 1)
  | '/' :: '-' :: rest => skipBlockComment rest (depth + 1)
  | _ :: rest => skipBlockComment rest depth
  | [] => ([], false)

/--
Keep only the significant characters of `s`: no comments, no whitespace, no
parentheses, no underscores.
-/
def normalizeBody (s : String) : String := Id.run do
  let mut out := ""
  let mut rest := s.toList
  while true do
    match rest with
    | [] => break
    | c :: cs =>
      if c == '-' && cs.head? == some '-' then
        rest := cs.dropWhile (· != '\n')
      else if c == '/' && cs.head? == some '-' then
        let (r, closed) := skipBlockComment cs.tail 1
        rest := if closed then r else []
      else if c.isWhitespace || c == '(' || c == ')' || c == '_' then
        rest := cs
      else
        out := out.push c
        rest := cs
  return out

/--
Extract the characters of `src` in the half-open range `[start, stop)`, given as
raw positions.  Returns `none` if the range is malformed (e.g. produced by error
recovery), in which case the caller must fall back to replacing the body.
-/
partial def sliceOfRange? (src : String) (start stop : String.Pos.Raw) : Option String :=
  if stop < start || stop.atEnd src || start.atEnd src then
    none
  else
    go start []
where
  go (p : String.Pos.Raw) (acc : List Char) : Option String :=
    if p == stop then
      some <| String.ofList acc.reverse
    else if p.atEnd src then
      none
    else
      go (p.next src) (p.get src :: acc)

/-- The raw source text of the right-hand side node `rhs`, if it has a usable range. -/
def bodyText? (src : String) (rhs : Syntax) : Option String :=
  match rhs.getRange? (canonicalOnly := true) with
  | some range => sliceOfRange? src range.start range.stop
  | none => none

/--
Has this right-hand side already been replaced?  The `declVal*` node's range
includes the leading trivia of the `:=` token, so re-splicing `body` over an
already-replaced body would append one space per run.  Skipping those bodies
makes repeated in-place runs exact no-ops.
-/
def isAlreadyReplaced? (body : String) (src : String) (rhs : Syntax) : Bool :=
  let needle := normalizeBody body
  needle != "" && (bodyText? src rhs).any fun text => (normalizeBody text).endsWith needle

/-- Find the proof-body node (right-hand side) of a theorem-like command. -/
partial def findRhs? (stx : Syntax) : Option Syntax :=
  if isTheoremRhsNode stx then
    some stx
  else
    stx.getArgs.findSome? findRhs?

/-- Find the direct `theorem` command inside a `declaration` node. -/
def findTheorem? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Command.theorem then
    some stx
  else
    stx.getArgs.find? (·.isOfKind ``Parser.Command.theorem)

/-- Find the identifier node inside a declaration syntax. -/
partial def findDeclId? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Parser.Command.declId && stx.getNumArgs > 0 && stx[0].isIdent then
    some stx[0].getId
  else
    stx.getArgs.findSome? findDeclId?

/-- Check if syntax node represents `simps` attribute. -/
partial def isSimpsAttrNode (stx : Syntax) : Bool :=
  let k := stx.getKind
  if k == `Lean.Parser.Attr.simps || k == `simps || k == `Mathlib.Tactic.Simps.simps then
    true
  else if stx.isAtom && stx.getAtomVal == "simps" then
    true
  else if stx.isIdent then
    let s := stx.getId.toString
    s == "simps" || s.startsWith "simps!" || s.startsWith "simps?"
  else
    false

/-- Check if syntax `stx` contains a `simps` attribute. -/
partial def containsSimpsAttr (stx : Syntax) : Bool :=
  if isSimpsAttrNode stx then
    true
  else
    stx.getArgs.any containsSimpsAttr

/-- Find the modifiers node of a declaration or lemma. -/
partial def findDeclModifiers? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Parser.Command.declModifiers then
    some stx
  else
    stx.getArgs.findSome? findDeclModifiers?

/-- Check if a declaration or lemma has `@[simps]` (or variant). -/
def hasSimps (stx : Syntax) : Bool :=
  match findDeclModifiers? stx with
  | some mods => containsSimpsAttr mods
  | none => false

/-- Reconstruct full declaration name. -/
def resolveName (currNamespace shortName : Name) : Name :=
  if (`_root_).isPrefixOf shortName then
    shortName.replacePrefix `_root_ Name.anonymous
  else
    currNamespace ++ shortName

/-- Check if declaration is a rfl theorem according to Lean's `isRflTheorem`. -/
def checkIsRflTheorem (env : Environment) (declName : Name) : IO Bool := do
  let opts : Options := ({} : Options).setBool `backward.dsimp.useDefEqAttr false
  let ctx : Core.Context := { fileName := "<isRfl>", fileMap := default, options := opts }
  let s : Core.State := { env }
  match (← ((Meta.isRflTheorem declName).toIO ctx s).toIO') with
  | Except.ok (b, _) => return b
  | Except.error _ => return false

/-- Determine whether `target` (a `theorem` or `lemma` node) is a `rfl` theorem using `isRflTheorem`. -/
def isRflDecl (env : Environment) (mainModule : Name) (currNamespace : Name) (target : Syntax) : IO Bool := do
  let some shortName := findDeclId? target | return false
  let fullName := resolveName currNamespace shortName
  let candidates := [fullName, Lean.mkPrivateNameCore mainModule fullName]
  for c in candidates do
    if (env.find? c).isSome then
      if ← checkIsRflTheorem env c then
        return true
  return false

/-- Build the edit replacing `stx`'s proof body with `newText`. -/
def mkEdit? (fileMap : FileMap) (newText : String) (stx : Syntax) : Option Lsp.TextEdit := do
  let range ← stx.getRange? (canonicalOnly := true)
  return { range := fileMap.utf8RangeToLspRange range, newText := newText }

/-- Has this equation right-hand side already been replaced with `| _ => sorry`? -/
def isEqnAlreadyReplaced? (src : String) (rhs : Syntax) : Bool :=
  (bodyText? src rhs).any fun text =>
    let norm := normalizeBody text
    norm == "|=>sorry" || norm == "|=>bysorry" || norm.endsWith "|=>sorry" || norm.endsWith "|=>bysorry"

/-- What `collect` accumulates while walking the commands of one file. -/
structure Acc where
  edits : Array Lsp.TextEdit := #[]
  replaced : Nat := 0
  keptRfl : Nat := 0
  keptSimps : Nat := 0
  /-- Names of `theorem`/`lemma` declarations whose proof body could not be
  located in the syntax tree (parse damage: the declaration parsed, but no
  `declVal*` node exists).  These are reported as errors instead of being
  silently skipped. -/
  noRhs : Array Name := #[]
  deriving Inhabited

/--
Collect proof-body edits from one command.
A declaration with `@[simps]` bumps `keptSimps` and produces no edit.
A declaration accepted by `isRflDecl` bumps `keptRfl` and produces no edit.

Simple right-hand sides (`declValSimple`) and structure instances
(`whereStructInst`) are replaced whole with `defaultBody` (` := by sorry`).

Equation right-hand sides (`declValEqns`) are replaced with a single
arm `armBody` (`| _ => sorry`), collapsing multiple arms and preserving
the layout indentation before `|`.
-/
partial def collect (src : String) (fileMap : FileMap) (body armBody : String)
    (env : Environment) (mainModule : Name) (currNamespace : Name)
    (acc : Acc) (stx : Syntax) : IO Acc := do
  let handle (thmOrLemma : Syntax) (rhs : Syntax) : IO Acc := do
    if hasSimps stx || hasSimps thmOrLemma then
      return { acc with keptSimps := acc.keptSimps + 1 }
    else if ← isRflDecl env mainModule currNamespace thmOrLemma then
      return { acc with keptRfl := acc.keptRfl + 1 }
    else if rhs.isOfKind ``Parser.Command.declValSimple || rhs.isOfKind ``Parser.Command.whereStructInst then
      if isAlreadyReplaced? body src rhs then
        return acc
      else
        match mkEdit? fileMap body rhs with
        | some e => return { acc with replaced := acc.replaced + 1, edits := acc.edits.push e }
        | none => return acc
    else if rhs.isOfKind ``Parser.Command.declValEqns then
      if isEqnAlreadyReplaced? src rhs then
        return acc
      else
        match mkEdit? fileMap armBody rhs with
        | some e => return { acc with replaced := acc.replaced + 1, edits := acc.edits.push e }
        | none => return acc
    else
      if isAlreadyReplaced? body src rhs then
        return acc
      else
        match mkEdit? fileMap body rhs with
        | some e => return { acc with replaced := acc.replaced + 1, edits := acc.edits.push e }
        | none => return acc
  if stx.isOfKind ``Parser.Command.declaration then
    match findTheorem? stx with
    | some thm =>
      match findRhs? thm with
      | some rhs => handle thm rhs
      | none =>
        -- The `theorem` parsed but has no proof-body node: parse damage
        -- (e.g. broken notation upstream in the file).  Record it so the
        -- caller can fail loudly instead of silently replacing nothing.
        -- Skip declarations without an identifier (e.g. syntax quotations).
        match findDeclId? thm with
        | some name => return { acc with noRhs := acc.noRhs.push name }
        | none => return acc
    | none => return acc
  else if isLemmaNode stx then
    match findRhs? stx with
    | some rhs => handle stx rhs
    | none =>
      match findDeclId? stx with
      | some name => return { acc with noRhs := acc.noRhs.push name }
      | none => return acc
  else if stx.isOfKind ``Parser.Command.withWeakNamespace && stx.getNumArgs > 2 then
    let innerNs := resolveName currNamespace (if stx[1].isIdent then stx[1].getId else Name.anonymous)
    collect src fileMap body armBody env mainModule innerNs acc stx[2]
  else if isCommandWrapper stx || stx.isOfKind nullKind then
    stx.getArgs.foldlM (fun a c => collect src fileMap body armBody env mainModule currNamespace a c) acc
  else
    return acc

/-- Process commands while recording current namespace from the command state. -/
partial def processCommandsWithNamespace : Frontend.FrontendM (Array (Syntax × Name) × Environment) := do
  let mut res := #[]
  while true do
    Frontend.updateCmdPos
    let cmdState ← Frontend.getCommandState
    let ns := cmdState.scopes.head!.currNamespace
    let ictx ← Frontend.getInputContext
    let pstate ← Frontend.getParserState
    let scope := cmdState.scopes.head!
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps, messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
    Frontend.setParserState ps
    Frontend.setMessages messages
    Frontend.elabCommandAtFrontend cmd
    res := res.push (cmd, ns)
    if Parser.isTerminalCommand cmd then break
  let finalEnv := (← Frontend.getCommandState).env
  return (res, finalEnv)

/-- Ensure search path includes Lake project and dependency build libraries. -/
def setupSearchPath : IO Unit := do
  let mut d ← IO.currentDir
  let mut root? : Option System.FilePath := none
  for _ in [:15] do
    if (← (d / "lakefile.lean").pathExists) || (← (d / "lakefile.toml").pathExists) then
      root? := some d
      break
    if let some parent := d.parent then
      d := parent
    else
      break
  if let some root := root? then
    let lakeDir : System.FilePath := root / ".lake"
    let buildLib : System.FilePath := lakeDir / "build" / "lib" / "lean"
    let mut sp : List System.FilePath := []
    if (← buildLib.pathExists) then
      sp := [buildLib]
    let packagesDir : System.FilePath := lakeDir / "packages"
    if (← packagesDir.pathExists) then
      for entry in (← packagesDir.readDir) do
        let pkgLib := entry.path / ".lake" / "build" / "lib" / "lean"
        if (← pkgLib.pathExists) then
          sp := pkgLib :: sp
    let curSp ← searchPathRef.get
    searchPathRef.set (sp ++ curSp)

/-- Elaborate `input`, returning top-level commands paired with their namespace,
final environment, and the error-severity messages of header/import processing
(empty when the imports loaded successfully). -/
def elaborateSource (input fileName : String) :
    IO (Array (Syntax × Name) × Environment × Name × Array Message) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let mainModuleName ← moduleNameOfFileName fileName none
  let (env, messages) ←
    Elab.processHeader header {} messages inputCtx (mainModule := mainModuleName)
  let headerErrs := messages.toList.filter (·.severity == MessageSeverity.error) |>.toArray
  let cmdState := Elab.Command.mkState env messages {}
  let frontendState : Frontend.State := { commandState := cmdState, parserState, cmdPos := parserState.pos }
  let ((cmds, finalEnv), _) ← (processCommandsWithNamespace { inputCtx }).run frontendState
  return (cmds, finalEnv, mainModuleName, headerErrs)

/-- Sort the edits, check that they are non-overlapping, and apply them right-to-left. -/
def applyEdits (fileMap : FileMap) (edits : Array Lsp.TextEdit) : Except String FileMap := do
  let sorted := edits.qsort fun a b => a.range < b.range
  let mut prev : Option Lsp.Range := none
  for e in sorted do
    if let some p := prev then
      if e.range.start < p.«end» then
        throw s!"overlapping edits {p.start}-{p.«end»} and {e.range.start}-{e.range.«end»}"
    prev := some e.range
  return sorted.foldr (fun e acc => Server.replaceLspRange acc e.range e.newText) fileMap

/-- Replace the proof bodies of `fileName`, overwriting the file itself. -/
unsafe def runInPlace (fileName : String) : IO UInt32 := do
  enableInitializersExecution
  setupSearchPath
  let src ← IO.FS.readFile fileName
  let src := src.crlfToLf
  let (commands, env, mainModule, headerErrs) ← elaborateSource src fileName
  -- Without the imported notation/statistics nothing parses correctly and the
  -- replacement would silently be a no-op (e.g. `Mathlib/Order/Bounds/OrderIso.lean`
  -- with missing oleans: every theorem lost its `declVal` node, `replaced 0`).
  -- Fail loudly instead so the user builds the missing dependencies first.
  if !headerErrs.isEmpty then
    for m in headerErrs do
      IO.eprintln s!"{fileName}: {← m.data.toString}"
    IO.eprintln s!"{fileName}: error: header/import processing failed; \
      the file cannot be processed reliably (run `lake build` on its imports first)"
    return 1
  let fileMap := src.toFileMap
  let mut acc : Acc := {}
  for (cmd, ns) in commands do
    acc ← collect src fileMap defaultBody eqnArmBody env mainModule ns acc cmd
  -- A `theorem`/`lemma` that parsed without a proof-body node means the file
  -- contains parse damage; replacing the rest would leave a half-processed file
  -- reported as success.  Fail loudly instead.
  if !acc.noRhs.isEmpty then
    for n in acc.noRhs do
      IO.eprintln s!"{fileName}: error: theorem/lemma `{n}` has no parseable proof body"
    IO.eprintln s!"{fileName}: error: {acc.noRhs.size} declaration(s) could not be processed; \
      no replacements were written"
    return 1
  match applyEdits fileMap acc.edits with
  | .ok out =>
    IO.FS.writeFile fileName out.source
    let simpsMsg := if acc.keptSimps > 0 then s!", kept {acc.keptSimps} `simps` proof(s)" else ""
    IO.println s!"{fileName}: replaced {acc.replaced} proof(s), kept {acc.keptRfl} `rfl` proof(s){simpsMsg}"
    return 0
  | .error e =>
    IO.eprintln e
    return 1

end ReplaceTheoremProofsRflV5

/-- `CertleExe FILE.lean` (exactly one file). -/
unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  -- The compiled executable is not run through Lean's driver, so it has to
  -- initialize the search path itself; `lean --run` already did this.
  initSearchPath (← findSysroot)
  ReplaceTheoremProofsRflV5.setupSearchPath
  match args with
  | [fileName] => return ← ReplaceTheoremProofsRflV5.runInPlace fileName
  | [] =>
    IO.eprintln "usage: CertleExe FILE.lean"
    IO.eprintln "error: expected exactly one input file, got 0"
    return 1
  | _ =>
    IO.eprintln "usage: CertleExe FILE.lean"
    IO.eprintln s!"error: expected exactly one input file, got {args.length}"
    return 1
