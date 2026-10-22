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
theorem addCommIff (a b : Nat) : a + b = b + a ↔ b + a = a + b  := by sorry

@[simp]
theorem leAddRight (a b : Nat) : a ≤ a + b  := by sorry

/-- Tactic-mode proof: must be replaced. -/
theorem mulTwoEq (n : Nat) : n * 2 = n + n  := by sorry

/-- `rfl`-proved: must be kept byte-identical by `isRflTheorem`. -/
theorem keepRfl (n : Nat) : n = n := rfl

end SigOrderIso
