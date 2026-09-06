import Mathlib.Order.UpperLower.CompleteLattice
import Mathlib.Order.UpperLower.Principal
import ThesisScratch.ForMathlib.Order.Hom.CompleteLattice

open OrderDual

class PreOrdCoh (α : Type*) extends Preorder α where
  Coh : α → α → Prop
  coh_of_le {x x' y y' : α} (hx : x' ≤ x) (hy : y' ≤ y) (h : Coh x y) : Coh x' y'
  coh_symm {x y : α} (h : Coh x y) : Coh y x

namespace PreOrdCoh

variable {α β : Type*} [PreOrdCoh α] [PreOrdCoh β]

infix:70 " ~ " => Coh

lemma Coh.symm {x y : α} (h : x ~ y) : y ~ x := coh_symm h

@[grind →]
lemma coh_of_le_left {x x' y : α} (hx : x' ≤ x) (h : x ~ y) : x' ~ y := coh_of_le hx le_rfl h

@[grind →]
lemma coh_of_le_right {x y y' : α} (hy : y' ≤ y) (h : x ~ y) : x ~ y' := coh_of_le le_rfl hy h

@[grind =]
lemma coh_symm_iff {x y : α} : x ~ y ↔ y ~ x := ⟨coh_symm, coh_symm⟩

instance : PreOrdCoh (α →o β) where
  Coh f g := ∀ (x y : α), x ~ y → f x ~ g y
  coh_of_le hf hg h := fun x y hxy => coh_of_le (hf x) (hg y) (h x y hxy)
  coh_symm h := fun x y hxy => (h y x hxy.symm).symm

instance : PreOrdCoh Unit where
  Coh _ _ := False
  coh_of_le _ _ := id
  coh_symm := id

end PreOrdCoh

open PreOrdCoh

structure CohHom (α β : Type*) [PreOrdCoh α] [PreOrdCoh β] extends OrderHom α β where
  map_coh' {x y : α} (h : x ~ y) : toFun x ~ toFun y

namespace CohHom

variable {α β : Type*} [PreOrdCoh α] [PreOrdCoh β]

instance : FunLike (CohHom α β) α β where
  coe f := f.toFun
  coe_injective f g := by cases f; cases g; simp

lemma map_coh {x y : α} (f : CohHom α β) (h : x ~ y) : f x ~ f y := f.map_coh' h

instance : Preorder (CohHom α β) := Preorder.lift DFunLike.coe

end CohHom

class LatCoh (α : Type*) extends CompleteLattice α, PreOrdCoh α where
  coh_sSup {x : α} {s : Set α} (h : ∀ y ∈ s, x ~ y) : x ~ sSup s

namespace LatCoh

variable {α β : Type*} [LatCoh α] [LatCoh β]

lemma coh_sSup_iff {x : α} {s : Set α} : x ~ sSup s ↔ ∀ y ∈ s, x ~ y := by
  refine ⟨?_, coh_sSup⟩
  intro h y hy
  exact coh_of_le_right (le_sSup hy) h

lemma sSup_coh_iff {s : Set α} {y : α} : sSup s ~ y ↔ ∀ x ∈ s, x ~ y := by
  simp_rw [coh_symm_iff, coh_sSup_iff]

lemma sSup_coh_sSup_iff {s t : Set α} : sSup s ~ sSup t ↔ ∀ x ∈ s, ∀ y ∈ t, x ~ y := by
  simp_rw [coh_sSup_iff, sSup_coh_iff]
  grind

def cohAdj (x : α) : α := sSup {y | x ~ y}

prefix:80 "*" => cohAdj

lemma coh_cohAdj (x : α) : x ~ *x := by grind [cohAdj, coh_sSup_iff]

lemma coh_iff_le_cohAdj_left {x y : α} : x ~ y ↔ y ≤ *x :=
  ⟨le_sSup, (coh_of_le_right · (coh_cohAdj x))⟩

lemma coh_iff_le_cohAdj_right {x y : α} : x ~ y ↔ x ≤ *y := by
  rw [coh_symm_iff, coh_iff_le_cohAdj_left]

instance : LatCoh αᵒᵈ where
  Coh x y := ∀ (a b : α), a ~ b → a ≤ ofDual x ∨ b ≤ ofDual y
  coh_of_le := by
    intro x x' y y' hx hy h a b hab
    obtain (h | h) := h a b hab
    · exact Or.inl (h.trans hx)
    · exact Or.inr (h.trans hy)
  coh_symm := by
    intro x y h a b hab
    exact Or.symm <| h b a hab.symm
  coh_sSup := by
    intro x s h a b hab
    simp_all
    grind

lemma coh_orderDual_iff {x y : αᵒᵈ} : x ~ y ↔ ∀ (a b : α), a ~ b → a ≤ ofDual x ∨ b ≤ ofDual y :=
  Iff.rfl

lemma coh_orderDual_iff' {x y : αᵒᵈ} : x ~ y ↔ ∀ (a : α), a ≤ ofDual x ∨ *a ≤ ofDual y := by
  simp_rw [coh_orderDual_iff, coh_iff_le_cohAdj_left]
  grind

lemma cohAdj_orderDual (x : αᵒᵈ) : *x = toDual (sSup {b | ∃ a, ¬ a ≤ ofDual x ∧ b = *a}) := by
  apply eq_of_forall_le_iff
  intro y
  rw [←coh_iff_le_cohAdj_left, coh_orderDual_iff', le_toDual, sSup_le_iff]
  grind

instance {α : Type*} [PreOrdCoh α] : LatCoh (LowerSet α) where
  Coh s t := ∀ x ∈ s, ∀ y ∈ t, x ~ y
  coh_of_le hs ht h x hx y hy := h x (hs hx) y (ht hy)
  coh_symm h := by grind
  coh_sSup := by simp; grind

instance {α : Type*} [PreOrdCoh α] : LatCoh (LowerSet α) where
  Coh s t := ∀ x ∈ s, ∀ y ∈ t, x ~ y
  coh_of_le hs ht h x hx y hy := h x (hs hx) y (ht hy)
  coh_symm h := by grind
  coh_sSup := by simp; grind

lemma coh_lowerSet_iff {α : Type*} [PreOrdCoh α] {s t : LowerSet α} :
    s ~ t ↔ ∀ x ∈ s, ∀ y ∈ t, x ~ y := Iff.rfl

lemma cohAdj_lowerSet {α : Type*} [PreOrdCoh α] {s : LowerSet α} :
    ↑(*s : LowerSet α) = {y | ∀ x ∈ s, x ~ y} := by
  ext y
  rw [SetLike.mem_coe, ←LowerSet.Iic_le, ←coh_iff_le_cohAdj_left, coh_lowerSet_iff]
  constructor
  · intro h x hx
    exact h x hx y le_rfl
  · intro hy x hx y' hy'
    exact coh_of_le_right hy' (hy x hx)

lemma mem_cohAdj_lowerSet {α : Type*} [LatCoh α] {s : LowerSet α} {y : α} :
    y ∈ *s ↔ s ≤ LowerSet.Iic (*y) := by
  simp_rw [←SetLike.mem_coe, cohAdj_lowerSet, coh_iff_le_cohAdj_right]
  rfl

instance : LatCoh (sSupHom α β) where
  Coh f g := ∀ (x y : α), x ~ y → f x ~ g y
  coh_of_le hf hg h := fun x y hxy => coh_of_le (hf x) (hg y) (h x y hxy)
  coh_symm h := fun x y hxy => (h y x hxy.symm).symm
  coh_sSup := by
    intro f s hs x y hxy
    rw [sSupHom.apply_sSup, ←sSup_image, coh_sSup_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact hs a ha x y hxy

end LatCoh

open LatCoh

namespace CohHom

variable {α : Type*} [PreOrdCoh α]

protected def Iic : CohHom α (LowerSet α) where
  toFun x := LowerSet.Iic x
  monotone' x y h := LowerSet.Iic_le.mpr h
  map_coh' := by
    intro x y h a (ha : a ≤ x) b (hb : b ≤ y)
    exact coh_of_le ha hb h

lemma cohAdj_iic {α : Type*} [LatCoh α] {x : α} :
    *(LowerSet.Iic x) = LowerSet.Iic (*x) := by
  ext y
  rw [SetLike.mem_coe, LowerSet.coe_Iic, Set.mem_Iic, ←LowerSet.Iic_le, ←coh_iff_le_cohAdj_left,
    ←coh_iff_le_cohAdj_left, coh_lowerSet_iff]
  simp
  grind

lemma cohAdj_iic_orderDual {α : Type*} [LatCoh α] {x : α} :
    ((ofDual (cohAdj <| toDual <| LowerSet.Iic x) : LowerSet α) : Set α) = {y | ¬ *y ≤ x} := by
  ext y
  simp only [cohAdj_orderDual, ofDual_toDual, toDual_sSup, Set.preimage_ofPred_eq, ofDual_sInf,
    LowerSet.coe_sSup, Set.mem_ofPred_eq, Set.iUnion_exists, Set.biUnion_and',
    Set.iUnion_iUnion_eq_left, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
  have h_le_iic (s : LowerSet α) : s ≤ LowerSet.Iic x ↔ ∀ y ∈ s, y ≤ x := by rfl
  constructor
  · intro ⟨s, hs, hy⟩ hcon
    exact hs ((mem_cohAdj_lowerSet.mp hy).trans <| (LowerSet.Iic_strictMono _).monotone hcon)
  · intro h
    refine ⟨LowerSet.Iic (*y), ?_, ?_⟩
    · contrapose h
      exact le_of_forall_le h
    · rw [mem_cohAdj_lowerSet]

-- lemma Iic_coh_Iic_orderDual {α : Type*} [LatCoh α] {x y : α} :
--     toDual (CohHom.Iic x) ~ toDual (CohHom.Iic y) ↔ ∃ z, ¬ z ≤ x ∧ z ~ y := by
--   simp_rw [coh_orderDual_iff', ofDual_toDual]
--   contrapose!
  -- constructor
  -- · intro h

end CohHom
