import Mathlib.Topology.Partial
import ThesisScratch.ForMathlib.Data.PFun

open Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma pContinuous_def (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set Y, IsOpen s → IsOpen (f.preimage s) := Iff.rfl

lemma IsOpen.preimage_pfun {f : X →. Y} (hf : PContinuous f) {s : Set Y} (hs : IsOpen s) :
    IsOpen (f.preimage s) := hf s hs

lemma pContinuous_iff_isClosed (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set Y, IsClosed s → IsClosed (f.core s) := by
  simp_rw [pContinuous_def, ←isClosed_compl_iff, f.compl_preimage]
  constructor
  · intro h s hs
    specialize h sᶜ
    simp_all
  · grind

lemma IsClosed.core {f : X →. Y} (hf : PContinuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f.core s) := (pContinuous_iff_isClosed f).mp hf s hs

lemma PContinuous.image_closure {f : X →. Y} (hf : PContinuous f) (s : Set X) :
    f.image (closure s) ⊆ closure (f.image s) := by
  rw [f.image_subset_iff_subset_core, (isClosed_closure.core hf).closure_subset_iff]
  intro x hx
  exact f.core_mono subset_closure <| f.subset_core_image hx

lemma pContinuous_iff_image_closure_subset_closure_image (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set X, f.image (closure s) ⊆ closure (f.image s) := by
  refine ⟨PContinuous.image_closure, ?_⟩
  simp_rw [pContinuous_iff_isClosed, ←closure_subset_iff_isClosed, ←f.image_subset_iff_subset_core]
  intro h t ht
  exact (h <| f.core t).trans <| (closure_mono f.image_core_subset).trans ht
