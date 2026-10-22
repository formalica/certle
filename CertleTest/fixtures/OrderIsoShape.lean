import Certle

/-!
# Regression fixture: namespaced theorems with attributes (the OrderIso shape)

Mirrors `Mathlib/Order/Bounds/OrderIso.lean`: a namespace, `variable`s,
attribute-carrying theorems (`@[to_dual]`-like), iff-statements and term-mode
proofs.  v4 must replace **all** non-`isRflTheorem` declarations — including
iff/term-mode proofs — and keep the `rfl` one untouched.
-/

namespace SigOrderIso

variable {α : Type}

/-- Symmetric-equality iff with a term-mode proof: must be replaced. -/
theorem addCommIff (a b : Nat) : a + b = b + a ↔ b + a = a + b :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]
theorem leAddRight (a b : Nat) : a ≤ a + b := Nat.le_add_right a b

/-- Tactic-mode proof: must be replaced. -/
theorem mulTwoEq (n : Nat) : n * 2 = n + n := by
  omega

/-- `rfl`-proved: must be kept byte-identical by `isRflTheorem`. -/
theorem keepRfl (n : Nat) : n = n := rfl

end SigOrderIso
