import Mathlib.Order.CompleteLattice.Basic

variable {α : Type*} [CompleteLattice α]

theorem sSup_Iic (x : α) : sSup (Set.Iic x) = x := by
  apply eq_of_forall_ge_iff
  simp
  grind

theorem sInf_Ici (x : α) : sInf (Set.Ici x) = x := by
  apply eq_of_forall_le_iff
  simp
  grind
