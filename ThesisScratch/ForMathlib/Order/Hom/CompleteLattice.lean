import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Data.Fintype.Order
import Mathlib.Order.GaloisConnection.Basic
import ThesisScratch.ForMathlib.Order.CompleteLattice.Basic

open OrderDual

variable {α β γ : Type*} [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

namespace sInfHom

protected lemma monotone (f : sInfHom α β) :
    Monotone f := OrderHomClass.monotone f

protected def dualOrderIso {α β : Type*} [CompleteLattice α] [CompleteLattice β] :
    sInfHom α β ≃o (sSupHom αᵒᵈ βᵒᵈ)ᵒᵈ :=
  (sInfHom.dual.trans toDual).toOrderIso
    (by
      intro f g h
      simp only [Equiv.trans_apply, ge_iff_le, toDual_le_toDual]
      intro x
      simpa using h (ofDual x)
    )
    (by
      intro f g h x
      simpa using ofDual_le_ofDual.mpr h (toDual x)
    )

@[simp] protected lemma dualOrderIso_apply_apply {f : sInfHom α β} {x : αᵒᵈ} :
    ofDual (sInfHom.dualOrderIso f) x = toDual (f x) := rfl

@[simp] protected lemma dualOrderIso_symm_apply_apply {f : (sSupHom αᵒᵈ βᵒᵈ)ᵒᵈ} {x : α} :
    sInfHom.dualOrderIso.symm f x = ofDual (ofDual f <| toDual x) := rfl

protected def precompHom (f : sInfHom α β) : sInfHom β γ →o sInfHom α γ where
  toFun := (·.comp f)
  monotone' g g' hle x := by simpa using hle (f x)

@[simp]
lemma precompHom_apply (f : sInfHom α β) (g : sInfHom β γ) : f.precompHom g = g.comp f := rfl

protected def postcompHom (f : sInfHom β γ) : sInfHom α β →o sInfHom α γ where
  toFun := f.comp
  monotone' g g' hle x := by simpa using f.monotone (hle x)

@[simp]
lemma postcompHom_apply (f : sInfHom β γ) (g : sInfHom α β) : f.postcompHom g = f.comp g := rfl

protected def toPropOrderIsoDual {α : Type*} [CompleteLattice α] :
    sInfHom α Prop ≃o αᵒᵈ where
  toFun f := toDual <| sInf {x | f x}
  invFun a := ⟨fun x => ofDual a ≤ x, by simp; grind⟩
  map_rel_iff' := by
    simp only [toDual_sInf, Set.preimage_ofPred_eq, Equiv.coe_fn_mk, sSup_le_iff, Set.mem_ofPred_eq,
      OrderDual.forall, ofDual_toDual, toDual_le, ofDual_sSup]
    intro f g
    constructor
    · intro h x hx
      apply g.monotone (h x hx)
      simp; grind
    · intro h a ha
      exact sInf_le <| h a ha
  left_inv := by
    intro f
    ext a
    simp only [toDual_sInf, Set.preimage_ofPred_eq, ofDual_sSup, ofDual_toDual, coe_mk]
    constructor
    · intro h
      apply f.monotone h
      simp; grind
    · exact sInf_le
  right_inv := sSup_Iic

@[simp] protected lemma toPropOrderIsoDual_apply {f : sInfHom α Prop} :
    f.toPropOrderIsoDual = toDual (sInf {x | f x}) := rfl

@[simp] protected lemma toPropOrderIsoDual_symm_apply_apply {a : αᵒᵈ} {x : α} :
    sInfHom.toPropOrderIsoDual.symm a x = (ofDual a ≤ x) := rfl

end sInfHom

def OrderIso.sInfHomCongrLeft (e : α ≃o β) : sInfHom α γ ≃o sInfHom β γ := by
  refine OrderIso.ofHomInv (sInfHom.precompHom e.symm) (sInfHom.precompHom e) ?_ ?_
  all_goals
    ext
    simp

@[simp] lemma OrderIso.sInfHomCongrLeft_apply {e : α ≃o β} {f : sInfHom α γ} :
    e.sInfHomCongrLeft f = f.comp e.symm := rfl

@[simp] lemma OrderIso.sInfHomCongrLeft_symm_apply {e : α ≃o β} {f : sInfHom β γ} :
    e.sInfHomCongrLeft.symm f = f.comp e := rfl

def OrderIso.sInfHomCongrRight (e : β ≃o γ) : sInfHom α β ≃o sInfHom α γ := by
  refine OrderIso.ofHomInv (sInfHom.postcompHom e) (sInfHom.postcompHom e.symm) ?_ ?_
  all_goals
    ext
    simp

@[simp] lemma OrderIso.sInfHomCongrRight_apply {e : β ≃o γ} {f : sInfHom α β} :
    e.sInfHomCongrRight f = (e : sInfHom β γ).comp f := rfl

@[simp] lemma OrderIso.sInfHomCongrRight_symm_apply {e : β ≃o γ} {f : sInfHom α γ} :
    e.sInfHomCongrRight.symm f = (e.symm : sInfHom γ β).comp f := rfl

namespace sSupHom

instance {α β : Type*} [SupSet α] [CompleteLattice β] : SupSet (sSupHom α β) where
  sSup s := ⟨fun x => ⨆ f ∈ s, f x, by
    intro t
    apply eq_of_forall_ge_iff
    simp
    grind
  ⟩

protected lemma apply_sSup {α β : Type*} [SupSet α] [CompleteLattice β]
  {s : Set (sSupHom α β)} {x : α} : (sSup s) x = ⨆ f ∈ s, f x := rfl

private instance {α β : Type*} [SupSet α] [CompleteLattice β] :
    CompleteSemilatticeSup (sSupHom α β) where
  isLUB_sSup s := by
    constructor
    · intro f hf x
      exact le_biSup (· x) hf
    · intro f hf x
      simp_rw [sSupHom.apply_sSup, iSup_le_iff]
      intro g hg
      exact hf hg x

instance {α β : Type*} [SupSet α] [CompleteLattice β] :
  CompleteLattice (sSupHom α β) := completeLatticeOfCompleteSemilatticeSup (sSupHom α β)

protected lemma monotone (f : sSupHom α β) : Monotone f := OrderHomClass.monotone f

protected def dualOrderIso : sSupHom α β ≃o (sInfHom αᵒᵈ βᵒᵈ)ᵒᵈ :=
  (sSupHom.dual.trans toDual).toOrderIso
    (by
      intro f g h
      simp only [Equiv.trans_apply, ge_iff_le, toDual_le_toDual]
      intro x
      simpa using h (ofDual x)
    )
    (by
      intro f g h x
      simpa using ofDual_le_ofDual.mpr h (toDual x)
    )

@[simp] lemma dualOrderIso_apply_apply {f : sSupHom α β} {x : αᵒᵈ} :
    ofDual (sSupHom.dualOrderIso f) x = toDual (f x) := rfl

@[simp] lemma dualOrderIso_symm_apply_apply {f : (sInfHom αᵒᵈ βᵒᵈ)ᵒᵈ} {x : α} :
    sSupHom.dualOrderIso.symm f x = ofDual (ofDual f <| toDual x) := rfl

protected def precompHom (f : sSupHom α β) : sSupHom β γ →o sSupHom α γ where
  toFun := (·.comp f)
  monotone' g g' hle x := by simpa using hle (f x)

@[simp]
lemma precompHom_apply (f : sSupHom α β) (g : sSupHom β γ) : f.precompHom g = g.comp f := rfl

protected def postcompHom (f : sSupHom β γ) : sSupHom α β →o sSupHom α γ where
  toFun := f.comp
  monotone' g g' hle x := by simpa using f.monotone (hle x)

@[simp]
lemma postcompHom_apply (f : sSupHom β γ) (g : sSupHom α β) : f.postcompHom g = f.comp g := rfl

protected noncomputable def toPropOrderIsoDual : sSupHom α Prop ≃o αᵒᵈ := by
  refine sSupHom.dualOrderIso.trans <| OrderIso.dual <|
    (OrderIso.compl (α := Prop)).symm.sInfHomCongrRight.trans <|
    sInfHom.toPropOrderIsoDual.trans (OrderIso.dualDual α).symm

@[simp] protected lemma toPropOrderIsoDual_apply {f : sSupHom α Prop} :
    f.toPropOrderIsoDual = toDual (sSup {x | ¬ f x}) := by rfl

@[simp] lemma toPropOrderIsoDual_symm_apply {x : αᵒᵈ} {a : α} :
    sSupHom.toPropOrderIsoDual.symm x a = ¬ (a ≤ ofDual x) := rfl

end sSupHom

def OrderIso.sSupHomCongrLeft (e : α ≃o β) : sSupHom α γ ≃o sSupHom β γ := by
  refine OrderIso.ofHomInv (sSupHom.precompHom e.symm) (sSupHom.precompHom e) ?_ ?_
  all_goals
    ext
    simp

def OrderIso.sSupHomCongrRight (e : β ≃o γ) : sSupHom α β ≃o sSupHom α γ := by
  refine OrderIso.ofHomInv (sSupHom.postcompHom e) (sSupHom.postcompHom e.symm) ?_ ?_
  all_goals
    ext
    simp
