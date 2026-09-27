import Mathlib.Order.ModularLattice

theorem isModularLattice_iff_sup_inf_le {α : Type*} [Lattice α] :
    IsModularLattice α ↔ ∀ {a b c : α}, a ⊓ (b ⊔ c) ≤ (a ⊔ c) ⊓ b ⊔ c := by
  constructor
  · intro h a b c
    rw [← h.sup_inf_sup_assoc]
    exact inf_le_inf_right (b ⊔ c) <| le_sup_left
  · intro h
    constructor
    intro x y z hle
    grw [inf_comm, sup_comm, h, sup_eq_left.mpr hle, sup_comm, inf_comm]
