import Mathlib.Data.PFun

namespace PFun

variable {α β : Type*}

lemma image_subset_iff_subset_core (f : α →. β) (s : Set α) (t : Set β) :
    f.image s ⊆ t ↔ s ⊆ f.core t := by
  grind [mem_core, mem_image]

lemma subset_core_image {f : α →. β} {s : Set α} : s ⊆ f.core (f.image s) := by
  rw [←image_subset_iff_subset_core]

lemma image_core_subset {f : α →. β} {t : Set β} : f.image (f.core t) ⊆ t := by
  rw [image_subset_iff_subset_core]

lemma compl_core {f : α →. β} {t : Set β} : (f.core t)ᶜ = f.preimage tᶜ := by grind [mem_core]

lemma compl_preimage {f : α →. β} {t : Set β} : (f.preimage t)ᶜ = f.core tᶜ := by
  rw [compl_eq_comm, compl_core, compl_compl]

lemma asSubtype_preimage {f : α →. β} {s : Set β} :
    f.asSubtype ⁻¹' s = Subtype.val ⁻¹' (f.preimage s) := by
  ext ⟨x, hx⟩
  simp_rw [Set.mem_preimage, asSubtype, fn_apply, mem_preimage]
  constructor
  · intro hmem
    exact ⟨(f x).get hx, hmem, Part.get_mem hx⟩
  · intro ⟨y, hy, hxy⟩
    rwa [Part.mem_unique (Part.get_mem hx) hxy]

lemma preimage_eq_asSubtype {f : α →. β} {s : Set β} :
    f.preimage s = Subtype.val '' (f.asSubtype ⁻¹' s) := by
  ext x
  simp only [mem_preimage, Set.mem_image, Set.mem_preimage, asSubtype, fn_apply, Subtype.exists,
    mem_dom, exists_and_right, exists_eq_right]
  constructor
  · intro ⟨y, hy, hxy⟩
    refine ⟨⟨y, hxy⟩, ?_⟩
    grind [Part.mem_unique, Part.get_mem]
  · intro ⟨⟨y, hy⟩, hmem⟩
    grind [Part.get_mem]

attribute [local instance] Classical.propDecidable in
lemma preimage_eq_evalOpt {f : α →. β} {s : Set β} :
    f.preimage s = f.evalOpt ⁻¹' (Option.some '' s) := by
  ext x
  simp_rw [Set.mem_preimage, evalOpt, Part.toOption]
  split_ifs with h <;> simp [h]
  · grind [Part.get_mem, Part.mem_unique]
  · grind [Part.dom_iff_mem]

end PFun
