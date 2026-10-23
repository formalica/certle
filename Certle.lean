/-
Copyright (c) 2026 The certle Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# The `certle` custom axiom

`certle` provides a single custom axiom, `certleAx`, used by the `certle`
executable to stand in for the proof of a theorem.

The axiom is restricted to `Prop`: `theorem` and `lemma` statements are always
propositions, and keeping the axiom out of `Type` prevents it from being used to
fabricate data.  Unlike `sorry` it is a *named*, *public* axiom, so that a
checker can look for it by name (e.g. via `#print axioms`) and so that the
replaced proof is attributed to `certle` rather than to Lean's built-in
`sorryAx`.
-/

namespace Certle

/-- Stand-in axiom for a replaced theorem proof.

This axiom is what `CertleExe.lean` splices in place of a theorem's original
proof body.  It is deliberately public and un-derived so that it can be
detected by name in the `#print axioms` output of a rewritten file. -/
public axiom certleAx (p : Prop) : p

/-- Public wrapper around `certleAx` for building replacement proof terms. -/
public def certleProof (p : Prop) : p := certleAx p

end Certle
