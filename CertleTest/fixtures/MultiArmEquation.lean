/-!
# Regression fixture: equation-style declarations with many arms

Mirrors `map_add_zsmul` in `Mathlib/Algebra/AddConstMap/Basic.lean`
and `mmap_cons` in `Mathlib/Data/Vector/Basic.lean`.  Declarations with
multiple arms (or complex pattern-matching arms) must be replaced with
a single wildcard sorry arm.
-/

theorem multiArmShape : ∀ (n : Nat), n + 0 = n
  | 0 => rfl
  | n + 1 => by rw [Nat.add_zero]

theorem vectorMmapConsShape {α} (a : α) :
    ∀ {n : Nat} (v : List α), a :: v = a :: v
  | _, [] => rfl
  | _, x :: xs => rfl
