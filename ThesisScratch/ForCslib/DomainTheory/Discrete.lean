import Mathlib.Order.Hom.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs

/-!-/

class DiscreteLE (α : Type*) [LE α] where
  le_iff_eq (x y : α) : x ≤ y ↔ x = y

attribute [simp] DiscreteLE.le_iff_eq

theorem OrderIso.discreteLE {α β : Type*} [LE α] [LE β] [DiscreteLE β] (e : α ≃o β) :
    DiscreteLE α where
  le_iff_eq := by simp [← e.le_iff_le]

section

variable {α β : Type*} [LE α] [DiscreteLE α]

instance : PartialOrder α where
  le_refl := by simp
  le_trans := by simp
  le_antisymm := by simp

theorem Monotone.of_discrete [Preorder β] (f : α → β) :
    Monotone f := fun _ _ ↦ by simp +contextual

def Equiv.orderIsoOfDiscreteLE [LE β] [DiscreteLE β] (e : α ≃ β) : α ≃o β :=
    e.toOrderIso (.of_discrete e) (.of_discrete e.symm)

@[simp]
lemma Equiv.orderIsoOfDiscreteLE_apply [LE β] [DiscreteLE β] (e : α ≃ β) (a : α) :
    e.orderIsoOfDiscreteLE a = e a := rfl

@[simp]
lemma Equiv.orderIsoOfDiscreteLE_symm_apply [LE β] [DiscreteLE β] (e : α ≃ β) (b : β) :
    e.symm.orderIsoOfDiscreteLE b = e.symm b := rfl

theorem DiscreteLE.mem_lowerBounds_iff {s : Set α} {x : α} :
    x ∈ lowerBounds s ↔ s ⊆ {x} := by simp [mem_lowerBounds]; grind

theorem DiscreteLE.mem_upperBounds_iff {s : Set α} {x : α} :
    x ∈ upperBounds s ↔ s ⊆ {x} := by simp [mem_upperBounds]

theorem DiscreteLE.bddBelow_iff_of_nonempty {s : Set α} (hne : s.Nonempty) :
    BddBelow s ↔ ∃ x, s = {x} := by
  simp_rw [BddBelow, Set.Nonempty, DiscreteLE.mem_lowerBounds_iff, Set.subset_singleton_iff_eq,
    hne.ne_empty, false_or]

theorem DiscreteLE.bddAbove_iff_of_nonempty {s : Set α} (hne : s.Nonempty) :
    BddAbove s ↔ ∃ x, s = {x} := by
  simp_rw [BddAbove, Set.Nonempty, DiscreteLE.mem_upperBounds_iff, Set.subset_singleton_iff_eq,
    hne.ne_empty, false_or]

open Classical in
@[to_dual]
noncomputable instance {α : Type*} [LE α] [DiscreteLE α] [hne : Nonempty α] : InfSet α where
  sInf s := if h : ∃ x, s = {x} then h.choose else hne.some

noncomputable instance {α : Type*} [LE α] [DiscreteLE α] [hne : Nonempty α] :
    ConditionallyCompletePartialOrder α where
  isGLB_csInf_of_directed s hdir hne hbdd := by
    obtain ⟨x, rfl⟩ := DiscreteLE.bddBelow_iff_of_nonempty hne |>.mp hbdd
    simp [sInf]
  isLUB_csSup_of_directed s hdir hne hbdd := by
    obtain ⟨x, rfl⟩ := DiscreteLE.bddAbove_iff_of_nonempty hne |>.mp hbdd
    simp [sSup]

noncomputable instance {α : Type*} [LE α] [DiscreteLE α] [hne : Nonempty α] :
    ConditionallyCompletePartialOrderSup α :=
  ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup

end

@[ext]
structure WithDiscreteLE (α : Type*) where
  toDiscrete :: (ofDiscrete : α)

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toDiscrete t x` being printed as `{ ofDiscrete := x }`
by `delabStructureInstance`. -/
@[app_delab WithDiscreteLE.toDiscrete]
meta def WithDiscreteLE.delabToDiscrete : Delab := delabApp

end Notation

@[simps]
def equivWithDiscreteLE (α : Type*) : α ≃ WithDiscreteLE α where
  toFun := WithDiscreteLE.toDiscrete
  invFun := WithDiscreteLE.ofDiscrete

instance {α : Type*} : LE (WithDiscreteLE α) where
  le a b := a = b

instance {α : Type*} : DiscreteLE (WithDiscreteLE α) where
  le_iff_eq _ _ := Iff.rfl

instance {α : Type*} [Nonempty α] : Nonempty (WithDiscreteLE α) :=
    (equivWithDiscreteLE α).symm.nonempty
