import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Sigma
import Mathlib.Order.OrdContinuous
import ThesisScratch.ForCslib.DomainTheory.Discrete
import Mathlib.Order.Atoms
import Mathlib.Data.Fintype.Defs

/-!-/

open Set ConditionallyCompletePartialOrderSup ConditionallyCompletePartialOrderInf

universe u

@[to_dual]
lemma IsLUB.ge_of_mem {α : Type*} [LE α] {a b : α} {s : Set α} (ha : IsLUB s a) (hb : b ∈ s) :
    b ≤ a := ha.1 hb

@[to_dual]
lemma IsLUB.le_of_forall_mem {α : Type*} [LE α] {a b : α} {s : Set α} (ha : IsLUB s a)
    (hb : ∀ x ∈ s, x ≤ b) : a ≤ b := ha.2 hb

@[to_dual]
lemma isLUB_bot_iff {α : Type*} [PartialOrder α] [OrderBot α] (s : Set α) :
    IsLUB s ⊥ ↔ s ⊆ {⊥} := by
  simp only [isLUB_iff_le_iff, bot_le, true_iff, subset_singleton_iff, eq_bot_iff]
  constructor
  · intro h x hx
    exact h ⊥ hx
  · intro h b x hx
    exact (h x hx).trans bot_le

@[to_dual]
lemma isLUB_iff_of_isCofinalFor {α : Type u_1} [Preorder α] {a : α} {s t : Set α}
    (hst : IsCofinalFor s t) (hts : IsCofinalFor t s) : IsLUB s a ↔ IsLUB t a := by
  suffices upperBounds t = upperBounds s by simp [isLUB_iff_le_iff, this]
  exact (upperBounds_mono_of_isCofinalFor hst).antisymm <| upperBounds_mono_of_isCofinalFor hts

@[to_dual]
theorem WithBot.leftOrdContinuous_coe (α : Type*) [Preorder α] :
    LeftOrdContinuous (↑· : α → WithBot α) := by
  intro s x ⟨y, hy⟩ hlub
  simp only [isLUB_iff_le_iff, WithBot.forall, WithBot.le_bot_iff, coe_ne_bot, false_iff,
    coe_le_coe]
  constructor
  · intro h
    exact WithBot.not_coe_le_bot _ <| h ⟨y, hy, rfl⟩
  · simp [mem_upperBounds, isLUB_le_iff hlub]

@[to_dual]
theorem WithBot.rightOrdContinuous_coe (α : Type*) [Preorder α] :
    RightOrdContinuous (↑· : α → WithBot α) := by
  intro s x ⟨y, hy⟩ hglb
  simpa [isGLB_iff_le_iff, WithBot.forall, mem_lowerBounds] using hglb

@[to_dual]
theorem WithBot.bddAbove_iff {α : Type*} [Preorder α] [hne : Nonempty α] {s : Set (WithBot α)} :
    BddAbove s ↔ BddAbove ((↑·) ⁻¹' s : Set α) := by
  simp only [bddAbove_def, WithBot.forall, bot_le, implies_true, true_and, mem_preimage,
    WithBot.exists, WithBot.le_bot_iff, coe_ne_bot, imp_false, coe_le_coe, or_iff_right_iff_imp]
  intro h
  exact ⟨hne.some, fun x' h' ↦ (h x' h').elim⟩

theorem WithBot.nonempty_preimage_of_notMem_bot {α : Type*} {s : Set (WithBot α)} (h : ⊥ ∉ s)
    (h₀ : s.Nonempty) : ((↑·) ⁻¹' s : Set α).Nonempty := by
  simp_all [Set.Nonempty, WithBot.exists]

@[to_dual]
noncomputable instance {α : Type*} [ConditionallyCompletePartialOrderSup α] :
    ConditionallyCompletePartialOrderSup (WithBot α) where
  isLUB_csSup_of_directed s hdir hne hbdd := by
    simp_rw [sSup]
    split_ifs with h
    · grind [isLUB_bot_iff]
    · replace ⟨a, h⟩ : ∃ a : α, ↑a ∈ s := by simp [WithBot.ne_bot_iff_exists] at h; grind
      have hcof : IsCofinalFor s ((↑· : α → WithBot α) '' (↑·) ⁻¹' s) := by
        intro x hx
        induction x with
        | bot => exact ⟨a, ⟨a, h, rfl⟩, bot_le⟩
        | coe x => exact ⟨x, ⟨x, hx, rfl⟩, le_rfl⟩
      rw [← isLUB_iff_of_isCofinalFor (.of_subset <| image_preimage_subset ..) hcof]
      refine WithBot.leftOrdContinuous_coe α ⟨a, h⟩ <|
        isLUB_csSup_of_directed _ ?_ ⟨a, h⟩ (WithBot.bddAbove_iff.mp hbdd)
      intro x (hx : ↑x ∈ s) y (hy : ↑y ∈ s)
      simpa [WithBot.exists] using hdir _ hx _ hy

@[to_dual]
noncomputable instance {α : Type*} [ConditionallyCompletePartialOrderInf α] :
    ConditionallyCompletePartialOrderInf (WithBot α) where
  isGLB_csInf_of_directed s hdir hne hbdd := by
    simp_rw [sInf]
    split_ifs with hbot hbdd'
    · apply IsLeast.isGLB
      simpa
    · have := isGLB_csInf_of_directed _ ?_ (WithBot.nonempty_preimage_of_notMem_bot hbot hne) hbdd'
      · simpa [isGLB_iff_le_iff, mem_lowerBounds, WithBot.forall, hbot] using this
      · intro x hx y hy
        simpa [WithBot.exists, hbot] using hdir _ hx _ hy
    · simpa [isGLB_iff_le_iff, WithBot.forall, mem_lowerBounds, hbot, not_bddBelow_iff'] using hbdd'

noncomputable instance {α : Type*} [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder (WithBot α) where

noncomputable instance {α : Type*} [ConditionallyCompletePartialOrder α] :
    ConditionallyCompletePartialOrder (WithTop α) where

def FlatDomain (α : Type*) := WithBot (WithDiscreteLE α)

namespace FlatDomain

variable {α β γ : Type*} {a b d : FlatDomain α}

instance : PartialOrder (FlatDomain α) :=
  inferInstanceAs <| PartialOrder <| WithBot (WithDiscreteLE α)

instance : OrderBot (FlatDomain α) :=
  inferInstanceAs <| OrderBot <| WithBot (WithDiscreteLE α)

noncomputable instance [Nonempty α] : ConditionallyCompletePartialOrder (FlatDomain α) :=
  inferInstanceAs <| ConditionallyCompletePartialOrder <| WithBot (WithDiscreteLE α)

@[coe, match_pattern]
def some (a : α) : FlatDomain α := WithBot.some (.toDiscrete a)

instance : Coe α (FlatDomain α) where
  coe := some

@[simp] lemma some_eq_coe (a : α) : FlatDomain.some a = a := rfl

lemma coe_injective : ((↑) : α → FlatDomain α).Injective :=
    WithBot.coe_injective.comp (equivWithDiscreteLE α).injective

@[simp, norm_cast]
lemma coe_inj {a b : α} : (a : FlatDomain α) = b ↔ a = b := coe_injective.eq_iff

@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : (a : FlatDomain α) → Sort u} (bot : C ⊥) (coe : ∀ a : α, C a) :
    ∀ a : FlatDomain α, C a
  | ⊥ => bot
  | (a : α) => coe a

@[simp]
lemma recBotCoe_bot {C : (a : FlatDomain α) → Sort u} (bot : C ⊥) (coe : ∀ a : α, C a) :
    recBotCoe (C := C) bot coe ⊥ = bot := rfl

@[simp]
lemma recBotCoe_coe {C : (a : FlatDomain α) → Sort u} (bot : C ⊥) (coe : ∀ a : α, C a) (a : α) :
    recBotCoe (C := C) bot coe a = coe a := rfl

lemma eq_bot_or_coe (a : FlatDomain α) : a = ⊥ ∨ ∃ b : α, a = b := by
  cases a with
  | bot => exact Or.inl rfl
  | coe a => exact Or.inr ⟨a, rfl⟩

def toOption (α : Type*) : FlatDomain α ≃ Option α where
  toFun a := a.recBotCoe none .some
  invFun a := a.rec ⊥ (↑)
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

@[simp] lemma toOption_apply_bot : toOption α ⊥ = none := rfl
@[simp] lemma toOption_apply_coe {a : α} : toOption α a = .some a := rfl
@[simp] lemma toOption_symm_apply_none : (toOption α).symm none = ⊥ := rfl
@[simp] lemma toOption_symm_apply_some {a : α} : (toOption α).symm (.some a) = a := rfl

instance [h : IsEmpty α] : Unique (FlatDomain α) where
  default := ⊥
  uniq a := by
    cases a with
    | bot => rfl
    | coe a => exact h.elim a

protected lemma «forall» {p : FlatDomain α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x := by
  refine ⟨fun h ↦ ⟨h ⊥, (h ·)⟩, ?_⟩
  intro ⟨hbot, hcoe⟩ a
  cases a with
  | bot => exact hbot
  | coe a => exact hcoe a

protected lemma «exists» {p : FlatDomain α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x := by
  constructor
  · intro ⟨a, ha⟩
    cases a with
    | bot => exact Or.inl ha
    | coe a => exact Or.inr ⟨a, ha⟩
  · rintro (h | ⟨a, ha⟩)
    · exact ⟨⊥, h⟩
    · exact ⟨a, ha⟩

@[simp]
lemma not_coe_eq_bot {a : α} : (a : FlatDomain α) ≠ ⊥ := by
  simp [← (toOption α).injective.ne_iff]

@[simp]
lemma not_bot_eq_coe {a : α} : (⊥ : FlatDomain α) ≠ a := not_coe_eq_bot.symm

lemma ne_bot_iff_exists : a ≠ ⊥ ↔ ∃ b : α, a = b := by
  cases a <;> simp

lemma bot_ne_iff_exists : ⊥ ≠ a ↔ ∃ b : α, a = b := by
  rw [ne_comm, ne_bot_iff_exists]

def map (f : α → β) : FlatDomain α → FlatDomain β := recBotCoe ⊥ (f ·)

@[simp] lemma map_bot (f : α → β) : map f (⊥ : FlatDomain α) = ⊥ := rfl

@[simp] lemma map_coe {f : α → β} {a : α} : map f a = f a := rfl

@[simp]
lemma map_eq_bot_iff (f : α → β) {a : FlatDomain α} : map f a = ⊥ ↔ a = ⊥ := by
  cases a <;> simp

def map₂ (f : α → β → γ) : FlatDomain α → FlatDomain β → FlatDomain γ :=
    recBotCoe ⊥ (fun a ↦ recBotCoe ⊥ (f a ·))

@[simp] lemma map₂_coe_coe {f : α → β → γ} {a : α} {b : β} : map₂ f a b = f a b := rfl

@[simp] lemma map₂_bot_left {f : α → β → γ} {b : FlatDomain β} : map₂ f ⊥ b = ⊥ := rfl

@[simp] lemma map₂_bot_right {f : α → β → γ} {a : FlatDomain α} : map₂ f a ⊥ = ⊥ := by
  cases a <;> rfl

lemma map₂_eq_bot {f : α → β → γ} {a : FlatDomain α} {b : FlatDomain β} :
  map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by cases a <;> cases b <;> simp

@[simp, norm_cast] lemma coe_le_coe {a b : α} : (a : FlatDomain α) ≤ b ↔ a = b := by
  constructor
  · rintro (_ | h)
    simpa using h
  · simp +contextual

def isBot : FlatDomain α → Bool := recBotCoe true (fun _ ↦ false)

lemma isBot_eq_true : isBot a ↔ a = ⊥ := by
  cases a <;> simp [isBot]

instance : Decidable (a = ⊥) := decidable_of_bool (isBot a) isBot_eq_true

def unFlatD (d : α) : FlatDomain α → α := recBotCoe d id

@[simp] lemma unFlatD_bot : unFlatD d ⊥ = d := rfl

@[simp] lemma unFlatD_coe {a : α} : unFlatD d a = a := rfl

def unFlat : (a : FlatDomain α) → a ≠ ⊥ → α
  | some a, _ => a

@[simp] lemma unFlat_coe (a : α) (h : (a : FlatDomain α) ≠ ⊥ := by decide) :
    unFlat a h = a := rfl

def mapFintype {ι : Type*} [Fintype ι] {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) : FlatDomain β :=
  if h : ∀ i, as i ≠ ⊥ then f (fun i ↦ unFlat (as i) (h i)) else ⊥

@[simp]
lemma mapFintype_coe {ι : Type*} [Fintype ι] {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, α i) : mapFintype f (fun i ↦ as i) = f as := by
  simp [mapFintype]

@[simp] lemma mapFintype_eq_bot {ι : Type*} [Fintype ι] {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) : mapFintype f as = ⊥ ↔ ∃ i, as i = ⊥ := by
  simp [mapFintype]

lemma mapFintype_of_eq_bot {ι : Type*} [Fintype ι] {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) {i : ι} (h : as i = ⊥) : mapFintype f as = ⊥ :=
  mapFintype_eq_bot f as |>.mpr ⟨i, h⟩

open Classical in
noncomputable def mapInd {ι : Type*} {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) : FlatDomain β :=
  if h : ∀ i, as i ≠ ⊥ then f (fun i ↦ unFlat (as i) (h i)) else ⊥

@[simp] lemma mapInd_coe {ι : Type*} {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, α i) : mapInd f (fun i ↦ as i) = f as := by
  simp [mapInd]

@[simp] lemma mapInd_eq_bot {ι : Type*} {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) : mapInd f as = ⊥ ↔ ∃ i, as i = ⊥ := by simp [mapInd]

lemma mapInd_of_eq_bot {ι : Type*} {α : ι → Type*} (f : (Π i, α i) → β)
    (as : Π i, FlatDomain (α i)) {i : ι} (h : as i = ⊥) : mapInd f as = ⊥ :=
  mapInd_eq_bot f as |>.mpr ⟨i, h⟩

lemma mapInd_eq_mapFintype {ι : Type*} [Fintype ι] {α : ι → Type*} (f : (Π i, α i) → β) :
    mapInd f = mapFintype f := by
  unfold mapInd mapFintype
  congr!

def _root_.List.foldFlat : List (FlatDomain α) → FlatDomain (List α)
  | [] => ([] : List α)
  | a :: l => .map₂ (· :: ·) a l.foldFlat

@[simp]
lemma _root_.List.foldFlat_empty : ([] : List (FlatDomain α)).foldFlat = ([] : List α) := rfl

@[simp]
lemma _root_.List.foldFlat_bot_cons {l : List (FlatDomain α)} : (⊥ :: l).foldFlat = ⊥ := rfl

@[simp]
lemma _root_.List.foldFlat_coe_cons {a : α} {l : List (FlatDomain α)} :
    (↑a :: l).foldFlat = l.foldFlat.map (a :: ·) := rfl

lemma _root_.List.foldFlat_map_coe {l : List α} : (l.map (↑· : α → FlatDomain α)).foldFlat = l := by
  induction l <;> simp_all

lemma _root_.List.foldFlat_eq_bot {l : List (FlatDomain α)} : l.foldFlat = ⊥ ↔ ⊥ ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a with
    | bot => simp
    | coe a => simpa

lemma le_def : a ≤ b ↔ a = ⊥ ∨ a = b := by
  revert a b
  simp [FlatDomain.forall]

lemma lt_def : a < b ↔ a = ⊥ ∧ b ≠ ⊥ := by
  simp +contextual [lt_iff_le_and_ne, le_def, or_and_right, ne_comm]

lemma lt_def' : a < b ↔ a = ⊥ ∧ ∃ c : α, b = c := by
  simp +contextual [lt_iff_le_and_ne, le_def, or_and_right, bot_ne_iff_exists]

lemma bot_lt_coe (a : α) : (⊥ : FlatDomain α) < a :=
  lt_def'.mpr ⟨rfl, a, rfl⟩

lemma covBy_iff : a ⋖ b ↔ a < b := by
  refine ⟨CovBy.lt, ?_⟩
  simp +contextual [lt_def, le_def, covBy_iff_lt_and_eq_or_eq]

lemma covBy_iff' : a ⋖ b ↔ a = ⊥ ∧ b ≠ ⊥ := covBy_iff.trans lt_def

lemma bot_covBy_coe (a : α) : (⊥ : FlatDomain α) ⋖ a := covBy_iff.mpr (bot_lt_coe a)

lemma isAtom_coe (a : α) : IsAtom (a : FlatDomain α) := (bot_covBy_coe a).isAtom

lemma isAtom_iff : IsAtom a ↔ a ≠ ⊥ := by
  simp [IsAtom, lt_def]

instance : IsStronglyAtomic (FlatDomain α) where
  exists_covBy_le_of_lt a b := by
    rw [lt_def, and_imp, ne_bot_iff_exists]
    rintro rfl ⟨b, rfl⟩
    exact ⟨b, bot_covBy_coe b, le_rfl⟩

instance : IsAtomistic (FlatDomain α) where
  isLUB_atoms a := by
    cases a with
    | bot => use ∅; simp
    | coe a => use {↑a}; simpa using isAtom_coe a

lemma disjoint_iff : Disjoint a b ↔ a = ⊥ ∨ a ≠ b := by
  cases a <;> simp [Disjoint, le_def]

lemma coe_disjoint_coe {a b : α} : a ≠ b ↔ Disjoint (a : FlatDomain α) b := by
  simp [disjoint_iff, coe_injective.ne_iff]

lemma map_monotone (f : α → β) : Monotone (FlatDomain.map f) := by
  simp_rw [Monotone, le_def]
  rintro _ _ (rfl | rfl)
  all_goals simp

lemma monotone_iff {f : FlatDomain α → FlatDomain β} :
    Monotone f ↔ f ⊥ = ⊥ ∨ ∃ b : β, ∀ a, f a = b := by
  constructor
  · intro h
    by_cases hbot : f ⊥ = ⊥
    · exact Or.inl hbot
    · obtain ⟨b, hb⟩ : ∃ b : β, f ⊥ = b := ne_bot_iff_exists.mp hbot
      refine Or.inr ⟨b, fun a ↦ ?_⟩
      cases a with
      | bot => exact hb
      | coe a =>
        symm
        simpa [hb, le_def] using h (@bot_le (FlatDomain α) _ _ a)
  · simp [Monotone, le_def, FlatDomain.forall]
    grind

end FlatDomain
