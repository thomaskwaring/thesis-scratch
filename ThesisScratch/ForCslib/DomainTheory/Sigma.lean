import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Sigma
import Mathlib.Order.OrdContinuous
import ThesisScratch.ForCslib.DomainTheory.Discrete
import Mathlib.Order.Atoms
import Mathlib.Data.Fintype.Defs

/-!-/

open Set ConditionallyCompletePartialOrderSup ConditionallyCompletePartialOrderInf

namespace Sigma

variable {ι : Type*} {α : ι → Type*}

@[to_dual existing mk_le_mk_iff]
theorem mk_ge_mk_iff [∀ i, LE (α i)] {i : ι} {a b : α i} : (⟨i, b⟩ : Sigma α) ≤ ⟨i, a⟩ ↔ b ≤ a :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LE.fiber _ _ _⟩

@[to_dual existing mk_lt_mk_iff]
theorem mk_gt_mk_iff [∀ i, LT (α i)] {i : ι} {a b : α i} : (⟨i, b⟩ : Sigma α) < ⟨i, a⟩ ↔ b < a :=
  ⟨fun ⟨_, _, _, h⟩ => h, Sigma.LT.fiber _ _ _⟩

@[to_dual existing le_def]
theorem ge_def [∀ i, LE (α i)] {a b : Σ i, α i} : a ≤ b ↔ ∃ h : b.1 = a.1, a.2 ≤ h.rec b.2 := by
  grind [le_def]

@[to_dual existing lt_def]
theorem gt_def [∀ i, LT (α i)] {a b : Σ i, α i} : a < b ↔ ∃ h : b.1 = a.1, a.2 < h.rec b.2 := by
  grind [lt_def]

private lemma _root_.DirectedOn.exists_subset_range [∀ i, LE (α i)] [Nonempty ι]
    {s : Set (Σ i, α i)} (hs : DirectedOn (· ≤ ·) s) : ∃ (i : ι), s ⊆ range (Sigma.mk i) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨⟨i, a⟩, ha⟩)
  · use Classical.arbitrary _, Set.empty_subset _
  · use i
    intro ⟨j, b⟩ hb
    obtain ⟨z, hz, haz, hbz⟩ := hs ⟨i, a⟩ ha ⟨j, b⟩ hb
    grind [Sigma.le_def]

@[to_dual existing DirectedOn.exists_subset_range]
private lemma _root_.DirectedOn.exists_subset_range' [∀ i, LE (α i)] [Nonempty ι]
    {s : Set (Σ i, α i)} (hs : DirectedOn (· ≥ ·) s) : ∃ (i : ι), s ⊆ range (Sigma.mk i) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨⟨i, a⟩, ha⟩)
  · use Classical.arbitrary _, Set.empty_subset _
  · use i
    intro ⟨j, b⟩ hb
    obtain ⟨z, hz, haz, hbz⟩ := hs ⟨i, a⟩ ha ⟨j, b⟩ hb
    grind [Sigma.le_def]

@[to_dual]
theorem leftOrdContinuous_mk [∀ i, Preorder (α i)] (i : ι) :
    LeftOrdContinuous (Sigma.mk i (β := α)) := by
  simp only [LeftOrdContinuous, isLUB_iff_le_iff, mem_upperBounds, le_def, mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, «forall»]
  intro s a hne h j b
  refine ⟨by grind, ?_⟩
  intro h'
  obtain ⟨rfl, -⟩ := h' hne.some hne.some_mem
  simpa [h] using h'

@[to_dual]
private lemma nonempty_of_mem_upperBounds [∀ i, LE (α i)] {i : ι} {a : α i} {s : Set (Σ i, α i)}
    (h : ⟨i, a⟩ ∈ upperBounds s) (hs : s.Nonempty) : (Sigma.mk i ⁻¹' s).Nonempty := by
  obtain ⟨⟨j, b⟩, hb⟩ := hs
  obtain ⟨(rfl : j = i), (hle : b ≤ a)⟩ := le_def.mp <| h hb
  use b, hb

@[to_dual]
private lemma subset_range_of_mem_upperBounds [∀ i, LE (α i)] {i : ι} {a : α i} {s : Set (Σ i, α i)}
    (h : ⟨i, a⟩ ∈ upperBounds s) : s ⊆ range (Sigma.mk i) := by
  intro ⟨j, b⟩ hb
  obtain ⟨(rfl : j = i), (hle : b ≤ a)⟩ := le_def.mp <| h hb
  use b

open Classical in
@[to_dual]
noncomputable instance [∀ i, SupSet (α i)] [Nonempty ι] : SupSet (Σ i, α i) where
  sSup s :=
    if h : ∃ (i : ι), s ⊆ range (Sigma.mk i) then
      ⟨h.choose, sSup <| Sigma.mk h.choose ⁻¹' s⟩ else
      ⟨Classical.arbitrary _, Classical.arbitrary _⟩

@[to_dual]
lemma sSup_eq_of_subset_range_mk [∀ i, SupSet (α i)] [Nonempty ι] {s : Set (Σ i, α i)} {i : ι}
    (hne : s.Nonempty) (hs : s ⊆ range (mk i)) : sSup s = ⟨i, sSup <| mk i ⁻¹' s⟩ := by
  have h' : ∃ i, s ⊆ range (mk i) := ⟨i, hs⟩
  have : h'.choose = i := by
    grind [hs hne.some_mem, h'.choose_spec hne.some_mem]
  simp_rw [sSup, h', reduceDIte]
  congr

@[to_dual]
lemma sSup_image_eq [∀ i, SupSet (α i)] [Nonempty ι] {i : ι} (s : Set (α i)) (hs : s.Nonempty) :
    sSup (mk i '' s) = ⟨i, sSup s⟩ := by
  convert sSup_eq_of_subset_range_mk (hs.image (mk i)) ?_
  all_goals grind

@[to_dual]
noncomputable instance [∀ i, ConditionallyCompletePartialOrderSup (α i)] [Nonempty ι] :
    ConditionallyCompletePartialOrderSup (Σ i, α i) where
  isLUB_csSup_of_directed s hdir hne hbdd := by
    obtain ⟨i, hi⟩ := hdir.exists_subset_range
    obtain ⟨s, rfl⟩ : ∃ s' : Set (α i), Sigma.mk i '' s' = s := ⟨Sigma.mk i ⁻¹' s, by grind⟩
    rw [sSup_image_eq _ hne.of_image]
    refine leftOrdContinuous_mk _ hne.of_image <|
      isLUB_csSup_of_directed _ ?_ hne.of_image ?_
    · intro x hx y hy
      obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := hdir ⟨i, x⟩ ⟨x, hx, rfl⟩ ⟨i, y⟩ ⟨y, hy, rfl⟩
      use z, hz
      simpa using hz'
    · obtain ⟨⟨j, b⟩, hb⟩ := hbdd
      obtain ⟨(rfl : i = j), -⟩ := le_def.mp <| hb ⟨_, hne.of_image.some_mem, rfl⟩
      exact ⟨b, fun x hx ↦ mk_le_mk_iff.mp <| hb ⟨x, hx, rfl⟩⟩

noncomputable instance [∀ i, ConditionallyCompletePartialOrder (α i)] [Nonempty ι] :
    ConditionallyCompletePartialOrder (Σ i, α i) where

end Sigma
