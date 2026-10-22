/-!
# Regression fixture: `where` declarations containing parent structure extensions

Mirrors `Function.completeDistribLatticeMinimalAxioms` in
`Mathlib/Order/CompleteBooleanAlgebra.lean`.  Parent structure extensions
(`__ := ...`) cannot be replaced branch-wise with `by sorry`; v4 must fall
back to replacing the whole `where` and its branches with `:= by sorry`.
-/

structure ParentProp (α : Type) : Prop where
  f (a : α) : a = a

structure ChildProp (α : Type) : Prop extends ParentProp α where
  g (a : α) : a = a

theorem parentStructShape (α : Type) : ChildProp α where
  __ := { f := fun a => rfl }
  g := fun a => rfl
