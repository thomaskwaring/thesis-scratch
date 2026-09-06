import Mathlib.Order.Partition.Basic
import Mathlib.Order.Atoms
import ThesisScratch.ForMathlib.Order.CompactlyGenerated.Basic
import ThesisScratch.ForMathlib.Data.Set.Lattice
import ThesisScratch.ForMathlib.Basic.Relation

open Order Set

namespace Partition

variable {α : Type*}

@[simp] lemma copy_refl [CompleteLattice α] {u : α} (P : Partition u) :
  P.copy (rfl : u = u) = P := rfl

@[simp] lemma copy_trans [CompleteLattice α] {u v w : α} (h : u = v) (h' : v = w)
  (P : Partition u) : (P.copy h).copy h' = P.copy (h.trans h') := rfl

lemma copy_injective [CompleteLattice α] {u v : α} {P Q : Partition u} (h : u = v)
    (h' : P.copy h = Q.copy h) : P = Q := by
  subst h
  simpa

@[simp] lemma copy_rel {s t : Set α} {P : Partition s} (h : s = t) :
    (P.copy h).Rel = P.Rel := by subst h; rfl

@[simp] lemma coe_mk [CompleteLattice α] {u : α} {s : Set α} (hindep : _root_.sSupIndep s)
    (hbot : ⊥ ∉ s) (hsup : sSup s = u) : (Partition.mk s hindep hbot hsup : Set α) = s := rfl

@[simp] lemma mem_mk [CompleteLattice α] {u : α} {s : Set α} (hindep : _root_.sSupIndep s)
    (hbot : ⊥ ∉ s) (hsup : sSup s = u) (v : α) :
    v ∈ Partition.mk s hindep hbot hsup ↔ v ∈ s := Iff.rfl

def ofFrame [Order.Frame α] {s : α} (parts : Set α) (hindep : parts.PairwiseDisjoint id)
    (hbot : ⊥ ∉ parts) (hsup : sSup parts = s) : Partition s where
  parts := parts
  sSupIndep' := sSupIndep_iff_pairwiseDisjoint.mpr hindep
  bot_notMem' := hbot
  sSup_eq' := hsup

def merge [Order.Frame α] {s : α} (P : Partition s) {u v : α}
    (hu : u ∈ P) (hv : v ∈ P) : Partition s := by
  refine ofFrame (insert (u ⊔ v) (P \ {u, v})) ?_ ?_ ?_
  · rintro a (rfl | ⟨ha, _⟩) b hb hab
    · simp_rw [Function.onFun, id_eq, ←sSup_pair]
      refine (P.sSupIndep.disjoint_sSup ?_ (Set.pair_subset hu hv) ?_).symm
      all_goals grind
    · rcases hb with (rfl | ⟨hb, hb'⟩)
      · simp_rw [Function.onFun, id_eq, ←sSup_pair]
        refine (P.sSupIndep.disjoint_sSup ?_ (Set.pair_subset hu hv) ?_)
        all_goals grind
      · exact P.disjoint ha hb hab
  · rintro (h | h)
    · grind [P.bot_notMem]
    · exact P.bot_notMem h.1
  · rw [le_antisymm_iff, sSup_le_iff]
    constructor
    · rintro b (rfl | hb)
      · exact sup_le (P.le_of_mem hu) (P.le_of_mem hv)
      · exact P.le_of_mem hb.1
    · simp_rw [←P.sSup_eq]
      apply sSup_le_sSup_of_isCofinalFor
      intro w hw
      by_cases hw' : (w ≤ u ⊔ v)
      · exact ⟨u ⊔ v, Set.mem_insert .., hw'⟩
      · refine ⟨w, Set.mem_insert_of_mem _ ⟨hw, ?_⟩, le_rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hw' (h ▸ le_sup_left), fun h => hw' (h ▸ le_sup_right)⟩

def discrete [Order.Frame α] [IsAtomistic α] (u : α) : Partition u where
  parts := {a | IsAtom a ∧ a ≤ u}
  sSupIndep' := by
    rw [sSupIndep_iff_pairwiseDisjoint]
    intro a ⟨ha, _⟩ b ⟨hb, _⟩
    exact ha.disjoint_of_ne hb
  bot_notMem' := by intro ⟨h, _⟩; exact false_of_ne h.ne_bot
  sSup_eq' := sSup_atoms_le_eq u

instance [Order.Frame α] [IsAtomistic α] (u : α) : OrderBot (Partition u) where
  bot := discrete u
  bot_le P := by
    intro a ⟨ha, hau⟩
    exact ha.le_sSup (s := P.parts) |>.mp (P.sSup_eq'.symm ▸ hau)

@[simp] lemma coe_bot [Order.Frame α] [IsAtomistic α] (u : α) :
    ((⊥ : Partition u) : Set α) = {a | IsAtom a ∧ a ≤ u} := rfl

@[simp] lemma mem_bot_iff [Order.Frame α] [IsAtomistic α] (u : α) (a : α) :
    a ∈ (⊥ : Partition u) ↔ IsAtom a ∧ a ≤ u := Iff.rfl

@[simp] lemma coe_bot_set (s : Set α) : ((⊥ : Partition s) : Set (Set α)) = {{x} | x ∈ s} := by
  grind [coe_bot, Set.isAtom_iff]

@[simp high + 1] lemma mem_bot_set (s t : Set α) : t ∈ (⊥ : Partition s) ↔ ∃ x ∈ s, t = {x} := by
  grind [mem_bot_iff, Set.isAtom_iff]

@[simp] lemma partOf_bot_of_mem {s : Set α} {x : α} (h : x ∈ s) :
    (⊥ : Partition s).partOf x = {x} := by
  refine eq_partOf_of_mem ?_ (mem_singleton _) |>.symm
  simpa

lemma injOn_partOf_bot (s : Set α) : s.InjOn (⊥ : Partition s).partOf := by
  intro x hx y hy
  simp [partOf_bot_of_mem hx, partOf_bot_of_mem hy]

@[simp] lemma rel_bot_iff (s : Set α) (x y : α) : (⊥ : Partition s).Rel x y ↔ x ∈ s ∧ x = y := by
  simp +contextual [Rel]

def sup_of_disjoint [Order.Frame α] {u v : α} (P : Partition u) (Q : Partition v)
    (h : Disjoint u v) : Partition (u ⊔ v) where
  parts := P.parts ∪ Q.parts
  sSupIndep' := P.sSupIndep'.union_of_disjoint_sSup_sSup Q.sSupIndep' <| by
    rwa [P.sSup_eq', Q.sSup_eq']
  bot_notMem' := (Or.elim · P.bot_notMem' Q.bot_notMem')
  sSup_eq' := by rw [sSup_union, P.sSup_eq', Q.sSup_eq']

def iSupOfDisjoint [Order.Frame α] {ι : Type*} {u : ι → α} {v : α} (P : (i : ι) → Partition (u i))
    (h : Set.univ.PairwiseDisjoint u) (hv : ⨆ i : ι, u i = v) : Partition v where
  parts := ⋃ i : ι, P i
  sSupIndep' := sSupIndep.iUnion_of_forall_sSupIndep_of_pairwiseDisjoint_sSup
    (fun i => (P i).sSupIndep) <| by
      intro i _ j _ hne
      simp_rw [Function.onFun, Function.comp_apply, sSup_eq]
      apply h <;> grind
  bot_notMem' := by rintro ⟨_, ⟨i, rfl⟩, hbot⟩; exact (P i).bot_notMem' hbot
  sSup_eq' := by simp [sSup_iUnion, hv]

@[simp] lemma iSupOfDisjoint_coe [Order.Frame α] {ι : Type*} {u : ι → α} {v : α}
    (P : (i : ι) → Partition (u i)) (h : Set.univ.PairwiseDisjoint u) (hv : ⨆ i : ι, u i = v) :
    (iSupOfDisjoint P h hv : Set α) = ⋃ i : ι, P i := rfl

@[simp] lemma mem_iSupOfDisjoint [Order.Frame α] {ι : Type*} {u : ι → α} {v : α}
    (P : (i : ι) → Partition (u i)) (h : Set.univ.PairwiseDisjoint u) (hv : ⨆ i : ι, u i = v)
    (w : α) : w ∈ iSupOfDisjoint P h hv ↔ ∃ i, w ∈ P i := by
  simp [← SetLike.mem_coe]

def bind [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α)) :
    Partition u :=
  iSupOfDisjoint Q (by
    intro ⟨v, hv⟩ _ ⟨v', hv'⟩ _ hne
    simpa [Function.onFun] using P.pairwiseDisjoint hv hv' (by grind))
    (by simp [← sSup_range])

@[simp] lemma coe_bind [Order.Frame α] {u : α} (P : Partition u)
    (Q : (v : P.parts) → Partition (v : α)) : (P.bind Q : Set α) = ⋃ v : (P : Set α), Q v := rfl

@[simp] lemma mem_bind [Order.Frame α] {u : α} (P : Partition u)
    (Q : (v : P.parts) → Partition (v : α)) (a : α) :
    a ∈ P.bind Q ↔ ∃ v : (P : Set α), a ∈ Q v := by simp [← SetLike.mem_coe]

lemma bind_le [Order.Frame α] {u : α} (P : Partition u) (Q : (v : P.parts) → Partition (v : α)) :
    P.bind Q ≤ P := by
  intro a ha
  obtain ⟨⟨v, hv⟩, ha⟩ : ∃ v : P, a ∈ Q v := mem_bind P Q a |>.mp ha
  use v, hv, (Q ⟨v, hv⟩).le_of_mem ha

def combine [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α] {u : α}
    (P : Partition u) (Q : Partition (P : Set α)) : Partition u where
  parts := sSup '' Q
  sSupIndep' := by
    rintro _ ⟨s, hs, rfl⟩
    refine (P.sSupIndep.disjoint_sSup_sSup (Q.subset_of_mem hs) ?_ (Q.sSupIndep hs)).mono_right ?_
    · intro x ⟨t, ⟨ht, _⟩, hxt⟩
      exact Q.subset_of_mem ht hxt
    · rw [sSup_le_iff, sSup_eq_sUnion]
      grind [sSup_le_sSup]
  bot_notMem' := by
    intro ⟨s, hs, h⟩
    obtain rfl := eq_singleton_bot_of_sSup_eq_bot_of_nonempty h (Q.nonempty_of_mem hs)
    exact P.bot_notMem <| Q.subset_of_mem hs <| mem_singleton ⊥
  sSup_eq' := by rw [sSup_image_sSup, ← sSup_eq_sUnion, Q.sSup_eq, P.sSup_eq]

lemma coe_combine [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α] {u : α}
    (P : Partition u) (Q : Partition (P : Set α)) : (P.combine Q : Set α) = sSup '' Q := rfl

lemma mem_combine [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α] {u : α}
    (P : Partition u) (Q : Partition (P : Set α)) (a : α) : a ∈ P.combine Q ↔ ∃ s ∈ Q, sSup s = a :=
  Iff.rfl

lemma le_combine [CompleteLattice α] [IsModularLattice α] [IsCompactlyGenerated α] {u : α}
    (P : Partition u) (Q : Partition (P : Set α)) : P ≤ P.combine Q := by
  intro a ha
  use! sSup (Q.partOf a), Q.partOf a, Q.partOf_mem ha, le_sSup (Q.mem_partOf ha)

def restrict' [Order.Frame α] {u : α} (P : Partition u) (v : α) : Partition (u ⊓ v) :=
  removeBot ((· ⊓ v) '' P) (by
    rw [sSupIndep_iff_pairwiseDisjoint]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
    apply Disjoint.inf_left; apply Disjoint.inf_right
    exact P.pairwiseDisjoint ha hb (by grind)
  )
  (by simp_rw [sSup_image, ←P.sSup_eq, sSup_inf_eq])

lemma coe_restrict' [Order.Frame α] {u : α} (P : Partition u) (v : α) :
    (P.restrict' v : Set α) = {a ⊓ v | a ∈ P} \ {⊥} := rfl

lemma mem_restrict' [Order.Frame α] {u : α} (P : Partition u) (v a : α) :
    a ∈ P.restrict' v ↔ (∃ a' ∈ P, a' ⊓ v = a) ∧ a ≠ ⊥ := Iff.rfl

lemma inf_mem_restrict' [Order.Frame α] {u a : α} (P : Partition u) (v : α) (ha : a ∈ P) :
  a ⊓ v ∈ P.restrict' v ↔ ¬ Disjoint a v := by grind [disjoint_iff_inf_le, mem_restrict']

lemma rel_restrict' {s t : Set α} (P : Partition s) :
    (P.restrict' t).Rel = Relation.Restrict P.Rel t t := by
  ext x y
  simp_rw [Rel, mem_restrict']
  constructor
  · rintro ⟨_, ⟨⟨u, hu, rfl⟩, hbot⟩, hx, hy⟩
    rw [Relation.restrict_iff_of_mem (mem_of_mem_inter_right hx) (mem_of_mem_inter_right hy)]
    use u, hu, mem_of_mem_inter_left hx, mem_of_mem_inter_left hy
  · intro ⟨⟨u, hu, hxu, hyu⟩, hx, hy⟩
    refine ⟨u ∩ t, ⟨⟨u, hu, rfl⟩, ?_⟩, ⟨hxu, hx⟩, ⟨hyu, hy⟩⟩
    exact ((u ∩ t).nonempty_of_mem ⟨hxu, hx⟩).ne_empty

lemma partOf_restrict'_of_mem {s t : Set α} (P : Partition s) {x : α} (hx : x ∈ t) :
    (P.restrict' t).partOf x = P.partOf x ∩ t := by
  ext y
  simp [rel_restrict', Relation.Restrict, hx]

def restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) : Partition v :=
  (P.restrict' v).copy (inf_of_le_right h)

lemma coe_restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) :
    (P.restrict h : Set α) = {a ⊓ v | a ∈ P} \ {⊥} := rfl

lemma mem_restrict [Order.Frame α] {u v : α} (P : Partition u) (h : v ≤ u) (a : α) :
    a ∈ P.restrict h ↔ (∃ a' ∈ P, a' ⊓ v = a) ∧ a ≠ ⊥ := Iff.rfl

lemma inf_mem_restrict [Order.Frame α] {u v a : α} (P : Partition u) (h : v ≤ u) (ha : a ∈ P) :
  a ⊓ v ∈ P.restrict h ↔ ¬ Disjoint a v := by grind [disjoint_iff_inf_le, mem_restrict]

lemma rel_restrict {s t : Set α} (P : Partition s) (h : t ⊆ s) :
    (P.restrict h).Rel = Relation.Restrict P.Rel t t := by
  rw [restrict, copy_rel, rel_restrict']

lemma partOf_restrict_of_mem {s t : Set α} (P : Partition s) (h : t ⊆ s) {x : α} (hx : x ∈ t) :
    (P.restrict h).partOf x = P.partOf x ∩ t := by
  ext y
  simp [rel_restrict, Relation.Restrict, hx]


section PER

open Relation PER

variable {r : α → α → Prop} [PER r]

def ofPER (r : α → α → Prop) [PER r] : Partition (dom r) where
  parts := {im r a | a ∈ dom r}
  sSupIndep' := by
    rintro _ ⟨a, _, rfl⟩
    rw [Set.disjoint_iff_forall_ne, Set.sSup_eq_sUnion]
    rintro b hb c ⟨_, ⟨⟨a', _, rfl⟩, hs⟩, hc⟩ rfl
    exact hs <| PER.im_eq_of_rel <| _root_.trans hb (symm hc)
  bot_notMem' := by
    intro ⟨a, h, h'⟩
    rw [Set.bot_eq_empty, im_eq_empty_iff] at h'
    exact h' h
  sSup_eq' := by
    ext x
    simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_ofPred_eq, exists_exists_and_eq_and]
    exact ⟨fun ⟨_, _, h⟩ => mem_dom_right h, fun h => ⟨x, h, mem_im_self.mpr h⟩⟩

@[simp] lemma coe_ofPER : (ofPER r : Set (Set α)) = im r '' dom r := rfl

@[simp] lemma mem_ofPER {s : Set α} : s ∈ ofPER r ↔ ∃ a ∈ dom r, im r a = s := Iff.rfl

lemma mem_partition' {s : Set α} : s ∈ ofPER r ↔ s ≠ ∅ ∧ ∃ a, im r a = s := by
  grind [mem_ofPER, im_eq_empty_iff]

@[simp] lemma partOf_ofPER_eq_im : (ofPER r).partOf x = im r x := by
  by_cases hx : x ∈ dom r
  · exact (ofPER r).eq_partOf_of_mem ⟨x, hx, rfl⟩ (mem_im_self.mpr hx) |>.symm
  · rwa [im_eq_empty_iff.mpr hx, Partition.partOf_eq_empty_iff]

@[simp] lemma rel_ofPER : (ofPER r).Rel = r := by
  ext x y
  constructor
  · intro ⟨_, ⟨z, hz, rfl⟩, hx, hy⟩
    exact rel_of_mem_im_of_mem_im hx hy
  · intro h
    use im r x, ⟨x, ⟨_, h⟩, rfl⟩, trans h (symm h), h

instance {α : Type*} {u : Set α} (P : Partition u) : PER P.Rel where

lemma dom_rel {s : Set α} (P : Partition s) : dom P.Rel = s := by
  ext x
  rw [PER.mem_dom_iff, rel_rfl_iff]

lemma ext_partOf {s : Set α} {P Q : Partition s} (h : P.partOf = Q.partOf) : P = Q := by
  ext t
  simp [mem_iff_exists_partOf, h]

lemma ext_rel {s : Set α} (P Q : Partition s) (h : P.Rel = Q.Rel) : P = Q := by
  apply ext_partOf
  ext
  simp [h]

lemma ofPER_rel {s : Set α} (P : Partition s) : (ofPER P.Rel).copy P.dom_rel = P := by
  apply ext_rel
  simp

end PER

end Partition
