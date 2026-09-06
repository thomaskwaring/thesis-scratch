import Mathlib.Logic.Equiv.Set
import Mathlib.Order.Hom.CompleteLattice
import ThesisScratch.ForMathlib.Partition.Basic

variable {α β : Type*}

namespace Partition

def mapInjective [CompleteLattice α] [CompleteLattice β] {f : α → β}
    (hf : f.Injective) (hf_sSup : ∀ s, f (sSup s) = sSup (f '' s))
    (hf_inf : ∀ a a', f (a ⊓ a') = f a ⊓ f a') {u : α} (P : Partition u) :
    Partition (f u) where
  parts := f '' P
  sSupIndep' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← Set.image_singleton, ← Set.image_sdiff hf, ← hf_sSup, disjoint_iff, ← hf_inf,
      disjoint_iff.mp <| P.sSupIndep hx]
    simp [← sSup_empty, hf_sSup]
  bot_notMem' := by
    intro ⟨x, hx, heq⟩
    have : f ⊥ = ⊥ := by simp [← sSup_empty, hf_sSup]
    exact P.bot_notMem' <| hf (this ▸ heq) ▸ hx
  sSup_eq' := by rw [← hf_sSup, P.sSup_eq]

@[simp] lemma coe_mapInjective [CompleteLattice α] [CompleteLattice β] {f : α → β}
    (hf : f.Injective) (hf_sSup : ∀ s, f (sSup s) = sSup (f '' s))
    (hf_inf : ∀ a a', f (a ⊓ a') = f a ⊓ f a') {u : α} (P : Partition u) :
    (P.mapInjective hf hf_sSup hf_inf : Set β) = f '' P := rfl

@[simp] lemma mem_mapInjective [CompleteLattice α] [CompleteLattice β] {f : α → β}
    (hf : f.Injective) (hf_sSup : ∀ s, f (sSup s) = sSup (f '' s))
    (hf_inf : ∀ a a', f (a ⊓ a') = f a ⊓ f a') {u : α} (P : Partition u) (b : β) :
    b ∈ P.mapInjective hf hf_sSup hf_inf ↔ ∃ a ∈ P, f a = b := Iff.rfl

def mapSetInjective {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s) :
    Partition (f '' s) :=
  P.mapInjective hf.image_injective (by simp [Set.image_sUnion]) (by simp [Set.image_inter hf])

@[simp] lemma coe_mapSetInjective {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s) :
  (P.mapSetInjective hf : Set (Set β)) = {f '' s | s ∈ P} := rfl

@[simp] lemma mem_mapSetInjective {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s)
    (t : Set β) : t ∈ P.mapSetInjective hf ↔ t ⊆ Set.range f ∧ f ⁻¹' t ∈ P := by
  rw [mapSetInjective, mem_mapInjective]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.image_subset_range f, (u.preimage_image_eq hf).symm ▸ hu⟩
  · intro ⟨htf, htP⟩
    use f ⁻¹' t, htP, t.image_preimage_eq_of_subset htf

lemma image_mem_mapSetInjective {f : α → β} (hf : f.Injective) {s : Set α} {P : Partition s}
    {t : Set α} (ht : t ∈ P) : f '' t ∈ P.mapSetInjective hf := ⟨t, ht, rfl⟩

@[simp] lemma partOf_mapSetInjective {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s)
    (x : α) : (P.mapSetInjective hf).partOf (f x) = f '' (P.partOf x) := by
  by_cases hx : x ∈ s
  · refine eq_partOf_of_mem (image_mem_mapSetInjective hf <| P.partOf_mem hx) ?_ |>.symm
    use x, mem_partOf hx
  · have : f x ∉ f '' s := by grind
    simp [partOf_eq_empty_iff.mpr hx, partOf_eq_empty_iff.mpr this]

@[simp] lemma mapSetInjective_rel {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s) :
    (P.mapSetInjective hf).Rel = Relation.Map P.Rel f f := by
  ext x y
  simp [Rel, ← SetLike.mem_coe, Relation.map_apply]
  grind

lemma mapSetInjective_rel_map_iff {f : α → β} (hf : f.Injective) {s : Set α} (P : Partition s)
    (x y : α) : (P.mapSetInjective hf).Rel (f x) (f y) ↔ P.Rel x y := by
  simp [Relation.map_apply]
  grind

def mapOrderIso [CompleteLattice α] [CompleteLattice β] (e : α ≃o β) {u : α}
    (P : Partition u) : Partition (e u) := P.mapInjective e.injective (by simp) e.map_inf

@[simp] lemma coe_mapOrderIso [CompleteLattice α] [CompleteLattice β] (e : α ≃o β) {u : α}
    (P : Partition u) : (P.mapOrderIso e : Set β) = e '' P := rfl

@[simp] lemma mem_mapOrderIso [CompleteLattice α] [CompleteLattice β] (e : α ≃o β) {u : α}
    (P : Partition u) (b : β) : b ∈ P.mapOrderIso e ↔ ∃ a ∈ P, e a = b := Iff.rfl

def mapOrderIsoTop [CompleteLattice α] [CompleteLattice β] (e : α ≃o β)
    (P : Partition (⊤ : α)) : Partition (⊤ : β) := (P.mapOrderIso e).copy e.map_top

@[simp] lemma coe_mapOrderIsoTop [CompleteLattice α] [CompleteLattice β] (e : α ≃o β)
    (P : Partition (⊤ : α)) : (P.mapOrderIsoTop e : Set β) = e '' P := rfl

@[simp] lemma mem_mapOrderIsoTop [CompleteLattice α] [CompleteLattice β] (e : α ≃o β)
    (P : Partition (⊤ : α)) (b : β) : b ∈ P.mapOrderIsoTop e ↔ ∃ a ∈ P, e a = b := Iff.rfl

def mapEquiv (e : α ≃ β) (P : Partition (.univ : Set α)) :
    Partition (.univ : Set β) := P.mapOrderIsoTop e.toOrderIsoSet

@[simp] lemma coe_mapEquiv (e : α ≃ β) (P : Partition (.univ : Set α)) :
    (P.mapEquiv e : Set (Set β)) = {e '' s | s ∈ P} := rfl

@[simp] lemma mem_mapEquiv (e : α ≃ β) (P : Partition (.univ : Set α)) (t : Set β) :
    t ∈ P.mapEquiv e ↔ e ⁻¹' t ∈ P := by
  simp [← SetLike.mem_coe, coe_mapEquiv, ← e.eq_preimage_iff_image_eq]

@[simp] lemma image_mem_mapEquiv (e : α ≃ β) (P : Partition (.univ : Set α)) (t : Set α) :
    e '' t ∈ P.mapEquiv e ↔ t ∈ P := by simp

@[simp] lemma partOf_mapEquiv_map (e : α ≃ β) (P : Partition (.univ : Set α)) (x : α) :
    (P.mapEquiv e).partOf (e x) = e '' (P.partOf x) := by
  refine eq_partOf_of_mem ?_ (by simp) |>.symm
  exact P.image_mem_mapEquiv e (P.partOf x) |>.mpr (P.partOf_mem (Set.mem_univ x))

lemma partOf_mapEquiv (e : α ≃ β) (P : Partition (.univ : Set α)) (x : β) :
    (P.mapEquiv e).partOf x = e '' (P.partOf <| e.symm x) := by
  rw [← e.apply_symm_apply x, partOf_mapEquiv_map]
  simp

@[simp] lemma mapEquiv_rel (e : α ≃ β) (P : Partition (.univ : Set α)) :
    (P.mapEquiv e).Rel = Relation.Map P.Rel e e := by
  ext x y
  rw [← mem_partOf_iff, ← e.apply_symm_apply x, partOf_mapEquiv_map, Relation.map_equiv_iff]
  simp

def sum {s : Set α} {t : Set β} (P : Partition s) (Q : Partition t) :
    Partition (Sum.inl '' s ∪ Sum.inr '' t) :=
  sup_of_disjoint (P.mapSetInjective Sum.inl_injective)
    (Q.mapSetInjective Sum.inr_injective) (by simp)

def sumUniv (P : Partition (.univ : Set α)) (Q : Partition (.univ : Set β)) :
    Partition (.univ : Set (α ⊕ β)) := (P.sum Q).copy (by simp)

def sigma {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) : Partition s :=
  iSupOfDisjoint (fun i => (P i).mapSetInjective sigma_mk_injective)
    (by grind [Set.PairwiseDisjoint, Set.Pairwise]) (Set.iUnion_image_preimage_sigma_mk_eq_self s)

@[simp] lemma coe_sigma {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) :
    (sigma P : Set (Set (Sigma α))) = {t | ∃ i t', t' ∈ (P i) ∧ Sigma.mk i '' t' = t} := by
  ext
  simp [sigma, iSupOfDisjoint]

@[simp] lemma mem_sigma {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) (t : Set (Sigma α)) :
    t ∈ sigma P ↔ ∃ i t', t' ∈ P i ∧ Sigma.mk i '' t' = t := by simp [← SetLike.mem_coe]

lemma image_mem_sigma {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) {i : ι} {t : Set (α i)} (ht : t ∈ P i) :
    Sigma.mk i '' t ∈ sigma P := by
  rw [mem_sigma]
  use i, t

@[simp] lemma partOf_sigma_mk {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) (i : ι) (x : α i) :
    (sigma P).partOf ⟨i, x⟩ = Sigma.mk i '' (P i).partOf x := by
  by_cases hmem : ⟨i, x⟩ ∈ s
  · refine eq_partOf_of_mem (image_mem_sigma P <| partOf_mem ?_) ?_ |>.symm
    all_goals simpa
  · rwa [partOf_eq_empty_iff.mpr hmem, Eq.comm, Set.image_eq_empty, partOf_eq_empty_iff]

@[simp] lemma sigma_rel_mk {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) {i : ι} {x y : α i} :
    (sigma P).Rel ⟨i, x⟩ ⟨i, y⟩ ↔ (P i).Rel x y := by
  simp [← mem_partOf_iff]

lemma fst_eq_of_sigma_rel {ι : Type*} {α : ι → Type*} {s : Set (Sigma α)}
    (P : (i : ι) → Partition (Sigma.mk i ⁻¹' s)) {x y : Sigma α} (h : (sigma P).Rel x y) :
    x.fst = y.fst := by
  rcases x with ⟨i, x⟩
  rw [← mem_partOf_iff, partOf_sigma_mk] at h
  grind

def prod {α β : Type*} [Order.Frame α] [Order.Frame β] {u : α} {v : β}
    (P : Partition u) (Q : Partition v) : Partition (u, v) := by
  refine sup_of_disjoint (α := α × β) (u := (u, ⊥)) (v := (⊥, v)) ?_ ?_ ?_
    |>.copy (by simp)
  · refine P.mapInjective (f := fun a => (a, (⊥ : β))) ?_ ?_ ?_
    · intro; grind
    · intro s; ext
      · simp only; congr; ext; simp
      · simp_rw [Prod.snd_sSup, ←Set.image_comp]
        simp [sSup_image]
    · simp
  · refine Q.mapInjective (f := fun b => ((⊥ : α), b)) ?_ ?_ ?_
    · intro; grind
    · intro s; ext
      · simp_rw [Prod.fst_sSup, ←Set.image_comp]
        simp [sSup_image]
      · simp only; congr; ext; simp
    · simp
  · simp [disjoint_iff]
    rfl

lemma coe_prod {α β : Type*} [Order.Frame α] [Order.Frame β] {u : α} {v : β}
    (P : Partition u) (Q : Partition v) :
    (P.prod Q : Set (α × β)) = {(a, ⊥) | a ∈ P} ∪ {(⊥, b) | b ∈ Q} := rfl

lemma mem_prod {α β : Type*} [Order.Frame α] [Order.Frame β] {u : α} {v : β}
    (P : Partition u) (Q : Partition v) (p : α × β) :
    p ∈ P.prod Q ↔ (∃ a ∈ P, (a, ⊥) = p) ∨ ∃ b ∈ Q, (⊥, b) = p := Iff.rfl

end Partition

namespace Pi

variable {ι : Type u} [DecidableEq ι] {α : ι → Type v} (i : ι)

def botSingle [∀ j, Bot (α j)] (a : α i) : Π i, α i := Function.update ⊥ i a

@[simp]
lemma botSingle_self [∀ j, Bot (α j)] (a : α i) : botSingle i a i = a := Function.update_self ..

lemma botSingle_of_ne [∀ j, Bot (α j)] {i j : ι} (h : j ≠ i) (a : α i) : botSingle i a j = ⊥ :=
  Function.update_of_ne h ..

lemma botSingle_injective [∀ j, Bot (α j)] : Function.Injective (botSingle (α := α) i) :=
  Function.update_injective ..

lemma botSingle_sSup [∀ j, CompleteLattice (α j)] (s : Set (α i)) :
    botSingle (α := α) i (sSup s) = sSup (botSingle i '' s) := by
  ext j
  by_cases h : j = i
  · subst j
    simp only [botSingle_self, sSup_apply, ← sSup_range]
    congr; ext; simp
  · rw [botSingle_of_ne h, sSup_apply, ← sSup_range, Eq.comm, sSup_eq_bot]
    simp [botSingle_of_ne h]

lemma botSingle_map_inf [∀ j, SemilatticeInf (α j)] [∀ j, OrderBot (α j)] (a b : α i) :
    botSingle (α := α) i (a ⊓ b) = botSingle i a ⊓ botSingle i b := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [botSingle_of_ne h]

lemma botSingle_inf_botSingle_of_ne [∀ j, SemilatticeInf (α j)] [∀ j, OrderBot (α j)] {i j : ι}
    (h : i ≠ j) (a : α i) (b : α j) : botSingle i a ⊓ botSingle j b = ⊥ := by
  ext k
  by_cases h : i = k
  · subst k; simp [botSingle_of_ne h]
  · simp [botSingle_of_ne <| Ne.intro fun a ↦ h a.symm]

lemma eq_sSup_botSingle [∀ j, CompleteLattice (α j)] (a : (i : ι) → α i) :
    ⨆ i, botSingle i (a i) = a := by
  ext j
  apply le_antisymm
  · rw [iSup_apply, iSup_le_iff]
    intro i
    by_cases h : j = i
    · subst j
      exact (botSingle_self ..).le
    · simp [botSingle_of_ne <| Ne.intro h]
  · rw [iSup_apply, ←botSingle_self j (a j)]
    exact le_iSup (fun i => botSingle i (a i) j) j

end Pi

namespace Partition

def pi {ι : Type u} [DecidableEq ι] {α : ι → Type u} [∀ i, Order.Frame (α i)]
    {u : (i : ι) → α i} (P : (i : ι) → Partition (u i)) : Partition u :=
  iSupOfDisjoint (u := fun i => Pi.botSingle i (u i))
    (fun i =>
      (P i).mapInjective (Pi.botSingle_injective ..) (Pi.botSingle_sSup i) (Pi.botSingle_map_inf i))
    (by
      intro i _ j _ h
      simpa [disjoint_iff] using Pi.botSingle_inf_botSingle_of_ne h (u i) (u j))
    (Pi.eq_sSup_botSingle u)

lemma coe_pi {ι : Type u} [DecidableEq ι] {α : ι → Type u} [∀ i, Order.Frame (α i)]
    {u : (i : ι) → α i} (P : (i : ι) → Partition (u i)) :
    (pi P : Set _) = {Pi.botSingle i a | (i : ι) (a ∈ P i)} := by
  simp only [pi, iSupOfDisjoint, SetLike.coe, mapInjective]
  ext x; simp

end Partition
