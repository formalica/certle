import Mathlib.Init
import Certle

/-!
# Regression fixture: quotation patterns containing `theorem` and `lemma`

Mirrors `Mathlib/Tactic/DeprecateTo.lean` where a `def` pattern matches on
syntax quotations like:
```lean
| `(command| $dm:declModifiers theorem $id:declId $d:declSig $v:declVal) => ...
```
v5 must skip these non-theorem quotation patterns and replace regular theorems
in the file with the Certle axiom.
-/

open Lean

set_option linter.unusedVariables false

def renameTheorem : TSyntax `command → TSyntax `Lean.Parser.Command.declId × TSyntax `command
  | `(command| $dm:declModifiers theorem $id:declId $d:declSig $v:declVal) => (id, default)
  | `(command| $dm:declModifiers lemma $id:declId $d:declSig $v:declVal) => (id, default)
  | a => (default, a)

/-- A regular theorem in the same file should still be replaced. -/
theorem regularTheorem (n : Nat) : n + 0 = n := by
  omega
