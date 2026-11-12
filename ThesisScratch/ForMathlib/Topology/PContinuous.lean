import Mathlib.Topology.Partial
import ThesisScratch.ForMathlib.Data.PFun
import Mathlib.Topology.Constructions

open Topology TopologicalSpace Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma pcontinuous_def (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set Y, IsOpen s → IsOpen (f.preimage s) := Iff.rfl

lemma IsOpen.preimage_pfun {f : X →. Y} (hf : PContinuous f) {s : Set Y} (hs : IsOpen s) :
    IsOpen (f.preimage s) := hf s hs

lemma pcontinuous_iff_isClosed (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set Y, IsClosed s → IsClosed (f.core s) := by
  simp_rw [pcontinuous_def, ← isClosed_compl_iff, f.compl_preimage]
  let e : Set Y ≃ Set Y :=
    {toFun := (·ᶜ), invFun := (·ᶜ), left_inv _ := by simp, right_inv _ := by simp}
  exact e.forall_congr_right (q := fun s ↦ IsClosed s → IsClosed (f.core s))

lemma IsClosed.core {f : X →. Y} (hf : PContinuous f) {s : Set Y} (hs : IsClosed s) :
    IsClosed (f.core s) := (pcontinuous_iff_isClosed f).mp hf s hs

lemma PContinuous.image_closure {f : X →. Y} (hf : PContinuous f) (s : Set X) :
    f.image (closure s) ⊆ closure (f.image s) := by
  rw [f.image_subset_iff_subset_core, (isClosed_closure.core hf).closure_subset_iff]
  intro x hx
  exact f.core_mono subset_closure <| f.subset_core_image hx

lemma pcontinuous_iff_image_closure_subset_closure_image (f : X →. Y) :
    PContinuous f ↔ ∀ s : Set X, f.image (closure s) ⊆ closure (f.image s) := by
  refine ⟨PContinuous.image_closure, ?_⟩
  simp_rw [pcontinuous_iff_isClosed, ← closure_subset_iff_isClosed,
    ← f.image_subset_iff_subset_core]
  intro h t ht
  exact (h <| f.core t).trans <| (closure_mono f.image_core_subset).trans ht

lemma PContinuous.continuous_asSubtype {f : X →. Y} (hf : PContinuous f) :
    Continuous f.asSubtype := by
  constructor
  intro s hs
  rw [IsEmbedding.subtypeVal.isInducing.isOpen_iff, f.preimage_asSubtype]
  use f.preimage s, hf s hs

lemma pcontinuous_iff_continuous_asSubtype (f : X →. Y) :
    PContinuous f ↔ IsOpen f.Dom ∧ Continuous f.asSubtype := by
  refine ⟨fun hf ↦ ⟨open_dom_of_pcontinuous hf, hf.continuous_asSubtype⟩, ?_⟩
  intro ⟨hdom, hf⟩ s hs
  rw [f.preimage_eq_asSubtype]
  apply IsEmbedding.subtypeVal.isOpenMap ?_ _ (hf.isOpen_preimage s hs)
  simpa [PFun.Dom] using hdom

local instance Option.instTopologicalSpace : TopologicalSpace (Option X) where
  IsOpen s := s = univ ∨ ∃ t : Set X, IsOpen t ∧ some '' t = s
  isOpen_univ := .inl rfl
  isOpen_inter s t := by
    rintro (rfl | ⟨s, hs, rfl⟩) (rfl | ⟨t, ht, rfl⟩)
    case inr.inr => exact .inr ⟨s ∩ t, hs.inter ht, image_inter <| some_injective X⟩
    all_goals grind
  isOpen_sUnion S hS := by
    by_cases huniv : univ ∈ S
    · grind
    · choose! t ht ht' using fun s hs ↦ (hS s hs).resolve_left <| ne_of_mem_of_not_mem hs huniv
      refine .inr ⟨⋃ s ∈ S, t s, isOpen_biUnion ht, ?_⟩
      rw [image_iUnion₂, sUnion_eq_biUnion]
      congrm ⋃ s, ⋃ hs, $(ht' s hs)

lemma isOpen_option_iff {s : Set (Option X)} :
  IsOpen s ↔ s = univ ∨ ∃ t, IsOpen t ∧ some '' t = s := Iff.rfl

variable (X) in
lemma Option.isOpenEmbedding_some : IsOpenEmbedding (@Option.some X) where
  eq_induced := TopologicalSpace.ext_iff.mpr fun s ↦ by
    simp [isOpen_induced_iff, isOpen_option_iff, (some_injective X).preimage_image]
    grind [isOpen_univ]
  injective := some_injective X
  isOpen_range := Or.inr ⟨univ, isOpen_univ, image_univ⟩

variable (X) in
lemma Option.continuous_some : Continuous (@Option.some X) := (isOpenEmbedding_some X).continuous

open Classical in
lemma pcontinuous_iff_evalOpt (f : X →. Y) : PContinuous f ↔ Continuous f.evalOpt := by
  simp [pcontinuous_def, continuous_def, isOpen_option_iff, f.preimage_eq_evalOpt]
