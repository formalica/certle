/-
Copyright (c) 2026 The certle Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The `certle` custom axiom

`certle` provides a single custom axiom, `certleAx`, used by the `certle`
executable to stand in for the proof of a theorem.

The axiom is declared exactly like Lean core's `sorryAx`: it inhabits every
type, so it can be used as the proof of any statement.  Unlike `sorry` it is a
*named*, *public* axiom, so that a checker can look for it by name (e.g. via
`#print axioms`) and so that the replaced proof is attributed to `certle`
rather than to Lean's built-in `sorry`.
-/

namespace Certle

/-- Stage-1 stand-in axiom for a replaced theorem proof (cf. `sorryAx`).

This axiom is what `CertleExe.lean` splices in place of a theorem's original
proof body.  It is deliberately public and un-derived so that it can be
detected by name in the `#print axioms` output of a rewritten file. -/
@[extern "lean_sorry", never_extract]
axiom certleAx (α : Sort u) : α

/-- Public wrapper around `certleAx`, used to build the replacement proof term. -/
def certleProof (α : Sort u) : α := certleAx α

end Certle
