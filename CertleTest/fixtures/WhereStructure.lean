/-!
# Regression fixture: declarations using `where` with branches

Mirrors `toCompleteDistribLattice` in `Mathlib/Order/CompleteBooleanAlgebra.lean`
and `span_singleton_eq_one_iff` in `Mathlib/Algebra/Algebra/Operations.lean`.
v4 must replace the entire `where` block and its branches with `:= by sorry`,
and the rewritten file must still compile.
-/

structure MyMinimalAxioms (α : Type) where
  inf_sSup_le_iSup_inf (a : α) (s : List α) : a = a
  iInf_sup_le_sup_sInf (a : α) (s : List α) : a = a

theorem toCompleteDistribLatticeShape (α : Type) : MyMinimalAxioms α where
  inf_sSup_le_iSup_inf a s := by
    rfl
  iInf_sup_le_sup_sInf a s := by
    rfl

theorem spanSingletonShape (p q : Prop) (h : p ↔ q) : p ↔ q where
  mp := by
    exact h.mp
  mpr := by
    exact h.mpr
