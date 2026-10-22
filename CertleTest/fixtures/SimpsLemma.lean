import Mathlib.Tactic.Simps.Basic

/-!
# Regression fixture: lemma declared with @[simps]

Mirrors `affine_combination` in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`.
v5 must skip theorems/lemmas declared with `simps`, keeping their original proof,
so that @[simps] does not fail due to a sorry body.
-/

structure MyPropStruct (p q : Prop) : Prop where
  hp : p
  hq : q

/-- A lemma declared with `@[simps]` whose proof is a structure instance. -/
@[simps]
lemma simpsLemmaWithWhere (p q : Prop) (hp : p) (hq : q) : MyPropStruct p q where
  hp := hp
  hq := hq

/-- A regular theorem without `@[simps]` in the same file should still be replaced by sorry. -/
theorem regularTheorem (n : Nat) : n + 0 = n := by
  omega
