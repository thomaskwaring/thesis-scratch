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

lemma IsCompactElement.exists_le_finsetSup_of_le_isLUB [SemilatticeSup α] [OrderBot α] {k : α}
    (hk : IsCompactElement k) {s : Set α} {u : α} (hu : IsLUB s u) (hle : k ≤ u) :
    ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id := by
  classical
  have hdir : DirectedOn (· ≤ ·) {x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id} := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    use (t ∪ t').sup id
    grind
  specialize hk {x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id} u ⟨⊥, ∅, by simp⟩ hdir
  simp only [Set.mem_ofPred_eq, ↓existsAndEq, and_true] at hk
  refine hk ⟨?_, ?_⟩ hle
  · rintro _ ⟨t, ht, rfl⟩
    exact Finset.sup_le fun x hx => hu.1 (ht hx)
  · intro u' hu'
    refine hu.2 (upperBounds_mono_set ?_ hu')
    intro x hx
    use {x}
    simpa

lemma isCompactElement_iff_exists_le_finsetSup_of_le_isLUB [SemilatticeSup α] [OrderBot α] {k : α} :
    IsCompactElement k ↔
      ∀ {s : Set α} {u : α}, IsLUB s u → k ≤ u → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id := by
  refine ⟨IsCompactElement.exists_le_finsetSup_of_le_isLUB, ?_⟩
  intro h s u hs hdir hu hle
  obtain ⟨t, ht, hsup⟩ := h hu hle
  obtain ⟨x, hx, htx⟩ := t.sup_le_of_le_directed s hs hdir (fun x hx => ⟨x, ht hx, le_rfl⟩)
  exact ⟨x, hx, hsup.trans htx⟩
