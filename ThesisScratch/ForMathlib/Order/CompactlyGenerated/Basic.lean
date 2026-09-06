import ThesisScratch.ForMathlib.Order.SupIndep
import Mathlib.Order.CompactlyGenerated.Basic

variable {α : Type*}

open CompleteLattice

theorem sSupIndep.disjoint_sSup_sSup {α : Type*} [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {s t u : Set α} (hs : sSupIndep s) (hts : t ⊆ s) (hus : u ⊆ s)
    (hdisj : Disjoint t u) : Disjoint (sSup t) (sSup u) := by
  rw [←biSup_preimage (f := Subtype.val (p := (· ∈ s))),
    ←biSup_preimage (f := Subtype.val (p := (· ∈ s)))]
  · exact (sSupIndep_iff s |>.mp hs).disjoint_biSup_biSup (hdisj.preimage _)
  · intro x hx
    use! x, hus hx
  · intro x hx
    use! x, hts hx

lemma IsAtom.isCompactElement [Order.Frame α] {x : α} (h : IsAtom x) : IsCompactElement x := by
  intro s u _ _ hu hx
  rwa [←hu.sSup_eq, IsAtom.le_sSup h] at hx

instance [Order.Frame α] [IsAtomistic α] : IsCompactlyGenerated α where
  exists_sSup_eq x := by
    obtain ⟨s, hx, hs⟩ := isLUB_atoms x
    refine ⟨s, fun a ha => (hs a ha).isCompactElement, hx.sSup_eq⟩

lemma IsCompactElement.exists_finset_eq_sup_of_eq_sup [CompleteLattice α] {x : α}
    (hx : IsCompactElement x) {s : Set α} (h : x = sSup s) :
    ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id := by
  obtain ⟨t, ht, hle⟩ := isCompactElement_iff_exists_le_sSup_of_le_sSup α x |>.mp hx s h.le
  use t, ht
  apply hle.antisymm
  rw [Finset.sup_eq_sSup_image, Set.image_id]
  exact (sSup_le_sSup ht).trans h.ge

lemma isCompactElement_iff_of_isAtomistic [Order.Frame α] [IsAtomistic α] (x : α) :
    IsCompactElement x ↔ ∃ t : Finset α, (∀ y ∈ t, IsAtom y) ∧ x = t.sup id := by
  constructor
  · intro h
    obtain ⟨s, heq, hs⟩ := eq_sSup_atoms x
    obtain ⟨t, ht, hsup⟩ := h.exists_finset_eq_sup_of_eq_sup heq
    use t, fun y hy => hs y (ht hy), hsup
  · rintro ⟨t, ht, rfl⟩
    apply isCompactElement_finsetSup t
    exact fun x hx => (ht x hx).isCompactElement
