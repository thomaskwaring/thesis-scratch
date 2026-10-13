import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.Common

class HuntingtonAlgebra (α : Type*) extends Max α, Compl α, Inhabited α where
  sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
  sup_comm (a b : α) : a ⊔ b = b ⊔ a
  huntington (a b : α) : (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ = a

namespace HuntingtonAlgebra

variable {α : Type*} [HuntingtonAlgebra α]

instance : Std.Associative (α := α) (· ⊔ ·) := ⟨sup_assoc⟩
instance : Std.Commutative (α := α) (· ⊔ ·) := ⟨sup_comm⟩

instance : Top α := ⟨default ⊔ defaultᶜ⟩
instance : Bot α := ⟨⊤ᶜ⟩

lemma compl_top : (⊤ : α)ᶜ = ⊥ := rfl

lemma sup_compl (a : α) : a ⊔ aᶜ = ⊤ := calc
  a ⊔ aᶜ = (aᶜ ⊔ defaultᶜ)ᶜ ⊔ (aᶜ ⊔ defaultᶜᶜ)ᶜ ⊔ ((aᶜᶜ ⊔ defaultᶜ)ᶜ ⊔ (aᶜᶜ ⊔ defaultᶜᶜ)ᶜ) := by
      simp [huntington]
  _ = (defaultᶜ ⊔ aᶜ)ᶜ ⊔ (defaultᶜ ⊔ aᶜᶜ)ᶜ ⊔ ((defaultᶜᶜ ⊔ aᶜ)ᶜ ⊔ (defaultᶜᶜ ⊔ aᶜᶜ)ᶜ) := by ac_rfl
  _ = default ⊔ defaultᶜ := by simp [huntington]

lemma compl_sup (a : α) : aᶜ ⊔ a = ⊤ := by rw [sup_comm, sup_compl]

lemma compl_compl (a : α) : aᶜᶜ = a := by calc
  aᶜᶜ = (aᶜᶜᶜ ⊔ aᶜ)ᶜ ⊔ (aᶜᶜᶜ ⊔ aᶜᶜ)ᶜ := (huntington aᶜᶜ aᶜ).symm
  _ = (aᶜ ⊔ aᶜᶜᶜ)ᶜ ⊔ ⊤ᶜ := by rw [← sup_compl aᶜᶜ]; ac_rfl
  _ = (aᶜ ⊔ aᶜᶜ)ᶜ ⊔ (aᶜ ⊔ aᶜᶜᶜ)ᶜ := by rw [sup_compl aᶜ, sup_comm]
  _ = a := huntington a aᶜᶜ

lemma compl_inj : Function.Injective (·ᶜ : α → α) := by
  intro a b (h : aᶜ = bᶜ)
  rw [← compl_compl a, h, compl_compl b]

lemma huntington' (a b : α) : (a ⊔ b)ᶜ ⊔ (a ⊔ bᶜ)ᶜ = aᶜ := by
    rw [← huntington aᶜ b, compl_compl a]

private lemma top_sup_top : (⊤ : α) ⊔ ⊤ = ⊤ := by
  have : (⊤ : α)ᶜ = (⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ := by nth_rw 1 [← huntington' ⊤ ⊤, sup_compl ⊤]
  calc
    ⊤ ⊔ ⊤ = ⊤ ⊔ ⊤ ⊔ ⊤ᶜ := by rw [sup_assoc, sup_compl]
    _ = ⊤ ⊔ ⊤ ⊔ (⊤ ⊔ ⊤)ᶜ ⊔ ⊤ᶜ := by nth_rw 1 [this, ← sup_assoc]
    _ = ⊤ := by rw [sup_compl, sup_compl]

private lemma bot_sup_bot : (⊥ : α) ⊔ ⊥ = ⊥ := calc
  ⊤ᶜ ⊔ ⊤ᶜ = (⊤ ⊔ ⊤)ᶜ ⊔ (⊤ ⊔ ⊤ᶜ)ᶜ := by rw [top_sup_top, sup_compl]
  _ = ⊤ᶜ := huntington' ⊤ ⊤

lemma sup_bot (a : α) : a ⊔ ⊥ = a := compl_inj <|
  calc
    (a ⊔ ⊤ᶜ)ᶜ = (a ⊔ ⊤ᶜ ⊔ ⊤)ᶜ ⊔ (a ⊔ ⊥ ⊔ ⊥)ᶜ := (huntington' (a ⊔ ⊤ᶜ) ⊤).symm
    _ = (a ⊔ ⊤)ᶜ ⊔ (a ⊔ ⊥)ᶜ := by rw [sup_assoc, compl_sup, sup_assoc, bot_sup_bot]
    _ = aᶜ := huntington' a ⊤

lemma bot_sup (a : α) : ⊥ ⊔ a = a := by rw [sup_comm, sup_bot]

lemma sup_idem (a : α) : a ⊔ a = a := compl_inj <|
  calc
    (a ⊔ a)ᶜ = (a ⊔ a)ᶜ ⊔ (a ⊔ aᶜ)ᶜ := by rw [sup_compl, compl_top, sup_bot]
    _ = aᶜ := huntington' a a

instance : Std.IdempotentOp (α := α) (· ⊔ ·) := ⟨sup_idem⟩

lemma sup_top (a : α) : a ⊔ ⊤ = ⊤ := by
  nth_rw 1 [← sup_compl a, ← sup_assoc, sup_idem a, sup_compl]

lemma top_sup (a : α) : ⊤ ⊔ a = ⊤ := by rw [sup_comm, sup_top]

lemma sup_compl_eq (a b : α) : a ⊔ bᶜ = a ⊔ (a ⊔ b)ᶜ := calc
  a ⊔ bᶜ = (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ ⊔ (b ⊔ a)ᶜ ⊔ (b ⊔ aᶜ)ᶜ := by
      rw [huntington, sup_assoc, huntington']
  _ = (aᶜ ⊔ b)ᶜ ⊔ (aᶜ ⊔ bᶜ)ᶜ ⊔ (a ⊔ b)ᶜ := by grind
  _ = a ⊔ (a ⊔ b)ᶜ := by rw [huntington]

instance : Min α where
  min a b := (aᶜ ⊔ bᶜ)ᶜ

lemma inf_eq (a b : α) : a ⊓ b = (aᶜ ⊔ bᶜ)ᶜ := rfl

lemma inf_assoc (a b c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by simp [inf_eq, compl_compl, sup_assoc]

lemma inf_comm (a b : α) : a ⊓ b = b ⊓ a := by rw [inf_eq, inf_eq, sup_comm]

lemma compl_inf_compl (a b : α) : aᶜ ⊓ bᶜ = (a ⊔ b)ᶜ := by rw [inf_eq, compl_compl, compl_compl]

lemma sup_inf_self (a b : α) : a ⊔ (a ⊓ b) = a := by
  rw [inf_eq, sup_compl_eq, ← sup_assoc, sup_compl, top_sup, compl_top, sup_bot]

lemma inf_sup_self (a b : α) : a ⊓ (a ⊔ b) = a := calc
  a ⊓ (a ⊔ b) = (aᶜ ⊔ (aᶜ ⊓ bᶜ))ᶜ := by rw [inf_eq, compl_inf_compl]
  _ = a := by rw [sup_inf_self, compl_compl]

lemma inf_compl (a : α) : a ⊓ aᶜ = ⊥ := by rw [inf_eq, compl_compl, compl_sup, compl_top]

instance : Lattice α :=
  Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self

instance : BoundedOrder α where
  le_top := sup_top
  bot_le := bot_sup

instance : DistribLattice α where
  le_sup_inf a b c := by
    suffices a ⊔ b ⊓ c = a ⊔ (a ⊔ b) ⊓ (a ⊔ c) from this ▸ le_sup_right
    calc
      a ⊔ (bᶜ ⊔ cᶜ)ᶜ = a ⊔ (a ⊔ bᶜ ⊔ cᶜ)ᶜ := by rw [sup_compl_eq, sup_assoc]
      _ = a ⊔ (a ⊔ bᶜ ⊔ (a ⊔ cᶜ))ᶜ := by ac_rfl
      _ = a ⊔ (a ⊔ (a ⊔ b)ᶜ ⊔ (a ⊔ c)ᶜ)ᶜ := by rw [sup_compl_eq a b, sup_compl_eq a c]; grind
      _ = a ⊔ (a ⊔ b) ⊓ (a ⊔ c) := by rw [sup_assoc, ← sup_compl_eq, inf_eq]

instance : BooleanAlgebra α where
  inf_compl_le_bot a := (inf_compl a).le
  top_le_sup_compl a := (sup_compl a).ge
  le_top a := le_top
  bot_le a := bot_le

end HuntingtonAlgebra
