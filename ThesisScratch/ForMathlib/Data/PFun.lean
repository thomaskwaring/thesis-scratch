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

end PFun
