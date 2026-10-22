/-!
# Regression fixture: equation-style theorem whose statement ends in a `do` block

This is the shape that crashed the first v4 rewrite (the issue reported for
`Mathlib/Data/Vector/Basic.lean`: unexpected doc-comment token error on the
declaration *after* `mmap_cons`).  The statement type ends with a
layout-sensitive `do` block and the value uses equation-style arms
`| pats => body`.  Replacing the whole `declValEqns` node with
` := by sorry` does not parse here; v4 must replace each arm body with
`by sorry` instead, and the doc-commented declaration below must survive
untouched.
-/

def mmapN {m : Type → Type} [Monad m] (f : Nat → m Nat) : List Nat → m (List Nat)
  | [] => pure []
  | x :: xs => do
    let h ← f x
    let t ← mmapN f xs
    pure (h :: t)

-- Statement ends with a `do` block, value is equation-style.  The whole
-- declaration is Pi-typed, so (like `mmap_cons` in Mathlib) `isRflTheorem`
-- is false even though the arm is `rfl` — v4 must replace the arm.
theorem mmapN_cons {m : Type → Type} [Monad m] (f : Nat → m Nat) (a : Nat) :
    ∀ (v : List Nat), mmapN f (a :: v) = do
      let h' ← f a
      let t' ← mmapN f v
      pure (h' :: t')
  | _ => rfl

/-- This doc comment must still parse after `mmapN_cons` was rewritten. -/
theorem afterDoBlock (n : Nat) : n = n := rfl
