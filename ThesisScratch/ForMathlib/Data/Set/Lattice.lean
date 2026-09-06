import Mathlib.Data.Set.Lattice

namespace Set

variable {α β : Type*}

theorem sSup_image_sSup [CompleteLattice α] (s : Set (Set α)) : sSup (sSup '' s) = sSup (⋃₀ s) := by
  rw [sSup_image, ← sSup_sUnion]

@[simp]
lemma sUnion_assoc (U : Set (Set (Set α))) : ⋃₀ ((⋃₀ ·) '' U) = ⋃₀ (⋃₀ U) := sSup_image_sSup U

end Set
