import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Data.Fintype.Order
import Mathlib.Order.GaloisConnection.Basic
import ThesisScratch.ForMathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

open OrderDual

variable {α β γ : Type*} [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

namespace sInfHom

@[to_dual]
protected lemma monotone (f : sInfHom α β) :
    Monotone f := OrderHomClass.monotone f

@[to_dual]
lemma le_def {f f' : sInfHom α β} : f ≤ f' ↔ ∀ x : α, f x ≤ f' x := Iff.rfl

@[to_dual]
lemma le_iff_le_coeFn {f f' : sInfHom α β} : f ≤ f' ↔ (f : α → β) ≤ f' := Iff.rfl

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
    (ofDual f.dualOrderIso) x = toDual (f <| ofDual x) := rfl

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

def _root_.OrderIso.sInfHomCongrLeft (e : α ≃o β) : sInfHom α γ ≃o sInfHom β γ := by
  refine OrderIso.ofHomInv (sInfHom.precompHom e.symm) (sInfHom.precompHom e) ?_ ?_
  all_goals
    ext
    simp

@[simp] lemma _root_.OrderIso.sInfHomCongrLeft_apply {e : α ≃o β} {f : sInfHom α γ} :
    e.sInfHomCongrLeft f = f.comp e.symm := rfl

@[simp] lemma _root_.OrderIso.sInfHomCongrLeft_symm_apply {e : α ≃o β} {f : sInfHom β γ} :
    e.sInfHomCongrLeft.symm f = f.comp e := rfl

def _root_.OrderIso.sInfHomCongrRight (e : β ≃o γ) : sInfHom α β ≃o sInfHom α γ := by
  refine OrderIso.ofHomInv (sInfHom.postcompHom e) (sInfHom.postcompHom e.symm) ?_ ?_
  all_goals
    ext
    simp

@[simp] lemma _root_.OrderIso.sInfHomCongrRight_apply {e : β ≃o γ} {f : sInfHom α β} :
    e.sInfHomCongrRight f = (e : sInfHom β γ).comp f := rfl

@[simp] lemma _root_.OrderIso.sInfHomCongrRight_symm_apply {e : β ≃o γ} {f : sInfHom α γ} :
    e.sInfHomCongrRight.symm f = (e.symm : sInfHom γ β).comp f := rfl

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
  left_inv f := by
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

namespace sSupHom

-- instance {α β : Type*} [SupSet α] [CompleteLattice β] : SupSet (sSupHom α β) where
--   sSup s := ⟨fun x => ⨆ f ∈ s, f x, by
--     intro t
--     apply eq_of_forall_ge_iff
--     simp
--     grind
--   ⟩

-- protected lemma apply_sSup {α β : Type*} [SupSet α] [CompleteLattice β]
--   {s : Set (sSupHom α β)} {x : α} : (sSup s) x = ⨆ f ∈ s, f x := rfl

-- private instance {α β : Type*} [SupSet α] [CompleteLattice β] :
--     CompleteSemilatticeSup (sSupHom α β) where
--   isLUB_sSup s := by
--     constructor
--     · intro f hf x
--       exact le_biSup (· x) hf
--     · intro f hf x
--       simp_rw [sSupHom.apply_sSup, iSup_le_iff]
--       intro g hg
--       exact hf hg x

-- instance {α β : Type*} [SupSet α] [CompleteLattice β] :
--   CompleteLattice (sSupHom α β) := completeLatticeOfCompleteSemilatticeSup (sSupHom α β)

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

def _root_.OrderIso.sSupHomCongrLeft (e : α ≃o β) : sSupHom α γ ≃o sSupHom β γ := by
  refine OrderIso.ofHomInv (sSupHom.precompHom e.symm) (sSupHom.precompHom e) ?_ ?_
  all_goals
    ext
    simp

lemma _root_.OrderIso.sSupHomCongrLeft_apply {e : α ≃o β} {f : sSupHom α γ} :
    e.sSupHomCongrLeft f = f.comp e.symm := rfl

@[simp] lemma _root_.OrderIso.sSupHomCongrLeft_symm_apply {e : α ≃o β} {f : sSupHom β γ} :
    e.sSupHomCongrLeft.symm f = f.comp e := rfl

def _root_.OrderIso.sSupHomCongrRight (e : β ≃o γ) : sSupHom α β ≃o sSupHom α γ := by
  refine OrderIso.ofHomInv (sSupHom.postcompHom e) (sSupHom.postcompHom e.symm) ?_ ?_
  all_goals
    ext
    simp

@[simp] lemma _root_.OrderIso.sSupHomCongrRight_apply {e : β ≃o γ} {f : sSupHom α β} :
    e.sSupHomCongrRight f = (e : sSupHom β γ).comp f := rfl

@[simp] lemma _root_.OrderIso.sSupHomCongrRight_symm_apply {e : β ≃o γ} {f : sSupHom α γ} :
    e.sSupHomCongrRight.symm f = (e.symm : sSupHom γ β).comp f := rfl


attribute [-instance] Prop.linearOrder Prop.instCompleteLinearOrder in
def toPropOrderIsoDual : sSupHom α Prop ≃o αᵒᵈ := by
  exact sSupHom.dualOrderIso.trans <| OrderIso.dual <|
    (OrderIso.compl (α := Prop)).symm.sInfHomCongrRight.trans <|
    sInfHom.toPropOrderIsoDual.trans (OrderIso.dualDual α).symm

@[simp] protected lemma toPropOrderIsoDual_apply {f : sSupHom α Prop} :
    f.toPropOrderIsoDual = toDual (sSup {x | ¬ f x}) := rfl

@[simp] lemma toPropOrderIsoDual_symm_apply {x : αᵒᵈ} {a : α} :
    sSupHom.toPropOrderIsoDual.symm x a = ¬ (a ≤ ofDual x) := rfl

end sSupHom

section Adj

@[to_dual] def upperAdj (f : α → β) : β → α := (sSup {x | f x ≤ ·})

@[to_dual (attr := simp)]
lemma upperAdj_apply (f : α → β) (y : β) : upperAdj f y = sSup {x | f x ≤ y} := rfl

@[to_dual (reorder := f g)]
lemma upperAdj_le_upperAdj {f g : α → β} (h : f ≤ g) : upperAdj g ≤ upperAdj f :=
  fun _ => sSup_le_sSup <| fun x hx => (h x).trans hx

@[to_dual]
lemma le_upperAdj_apply {f : α → β} {x : α} {y : β} (h : f x ≤ y) : x ≤ upperAdj f y := le_sSup h

variable {F : Type*} [FunLike F α β] [sSupHomClass F α β]

@[to_dual]
lemma upperAdj_gc (f : F) : GaloisConnection f (upperAdj f) := by
  intro x y
  refine ⟨le_upperAdj_apply, fun h => (OrderHomClass.monotone f h).trans ?_⟩
  simp

@[to_dual (attr := simp)]
lemma lowerAdj_upperAdj (f : F) : (lowerAdj <| upperAdj f) = f := by
  ext x
  refine GaloisConnection.l_unique ?_ (upperAdj_gc f) (fun _ => rfl)
  convert lowerAdj_gc (F := sInfHom β α) ⟨upperAdj f, fun _ => (upperAdj_gc f).u_sInf_eq_sInf_image⟩
  all_goals simp

@[to_dual (attr := simp) (reorder := f g) (rename := f ↔ g)]
lemma upperAdj_le_upperAdj_iff {f g : F} : upperAdj f ≤ upperAdj g ↔ (g : α → β) ≤ f := by
  refine ⟨fun h => ?_, fun h => upperAdj_le_upperAdj h⟩
  intro x
  rw [(upperAdj_gc g).le_iff_le]
  exact ((upperAdj_gc f).le_u_l x).trans (h _)

end Adj

namespace sSupHom

@[to_dual (attr := simps)]
def adjEquiv : sSupHom α β ≃ sInfHom β α where
  toFun f := ⟨upperAdj f, fun _ => (upperAdj_gc f).u_sInf_eq_sInf_image⟩
  invFun g := ⟨lowerAdj g, fun _ => (lowerAdj_gc g).l_sSup_eq_sSup_image⟩
  left_inv f := DFunLike.coe_injective <| lowerAdj_upperAdj f
  right_inv g := DFunLike.coe_injective <| upperAdj_lowerAdj g

@[to_dual]
def adjOrderIsoDual : sSupHom α β ≃o (sInfHom β α)ᵒᵈ where
  __ := adjEquiv.trans toDual
  map_rel_iff' := upperAdj_le_upperAdj_iff

end sSupHom

namespace GaloisConnection

variable {f : α → β} {g : β → α} (gc : GaloisConnection f g)

@[to_dual (reorder := f g, α β, 3 4) (rename := f ↔ g, α ↔ β)]
protected def sSupHom : sSupHom α β where
  toFun := f
  map_sSup' _ := gc.l_sSup_eq_sSup_image

@[to_dual (attr := simp) (reorder := f g, α β, 3 4) (rename := f ↔ g, α ↔ β)]
lemma sSupHom_apply (x : α) : gc.sSupHom x = f x := rfl

end GaloisConnection

namespace sSupHom

def orderIsoSubtypeMapBot {α β : Type*} [CompleteLinearOrder α] [Finite α]
    [CompleteLattice β] : sSupHom α β ≃o {f : α →o β // f ⊥ = ⊥} where
  toFun f := ⟨f, BotHomClass.map_bot f⟩
  invFun
    | ⟨f, hf⟩ => ⟨f, by
      intro s
      rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simpa
      · exact s.toFinite.map_sSup_of_monotone f.mono hs
    ⟩
  map_rel_iff' := by rfl

noncomputable def orderIsoFromBool : sSupHom Bool α ≃o α where
  toFun f := f true
  invFun a := ⟨Bool.rec ⊥ a, by
    intro s
    rcases s.eq_empty_or_nonempty with (rfl | hs)
    · simp
    · refine s.toFinite.map_sSup_of_monotone ?_ hs
      rintro (_ | _) (_ | _)
      all_goals simp
  ⟩
  left_inv f := by
    ext (_ | _)
    · simp [←bot_eq_false]
    · simp
  map_rel_iff' {f g} := by
    constructor
    · rintro h (_ | _)
      · simp [←bot_eq_false]
      · exact h
    · exact (· true)

example (α : Type*) [CompleteLattice α] [DecidableEq α] [Nontrivial α] (p : Prop) : Decidable p :=
  have : sSup {a | p ∧ a = ⊤} = (⊤ : α) ↔ p := by by_cases h : p <;> simp [h]
  decidable_of_iff _ this


end sSupHom
