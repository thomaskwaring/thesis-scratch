import ThesisScratch.ForMathlib.RelationAlgebra.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Order.Disjoint

open Allegory

class AltAllegory (α : Type*) extends BooleanAlgebra α, Monoid α, StarMul α where
  mul_sup (a b c : α) : a * (b ⊔ c) = a * b ⊔ a * c
  star_sup (a b : α) : star (a ⊔ b) = star a ⊔ star b
  star_mul_compl_le (a b : α) : star a * (a * b)ᶜ ≤ bᶜ

namespace AltAllegory

instance {α : Type*} [BooleanAllegory α] : AltAllegory α where
  star := conv
  star_involutive := conv_conv
  star_mul := conv_mul
  mul_sup := UnionAllegory.mul_sup
  star_sup := conv_sup
  star_mul_compl_le := conv_mul_compl_mul_le_compl

variable {α : Type*} [AltAllegory α]

instance : MulLeftMono α where
  elim a b c h := by simp [← sup_eq_left, ← mul_sup, sup_eq_left.mpr h]

lemma sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c := by
  apply star_involutive.injective
  simp [star_mul, star_sup, mul_sup]

instance : MulRightMono α where
  elim a b c h := by simp [← sup_eq_left, ← sup_mul, sup_eq_left.mpr h]

@[instance_reducible]
private def toBooleanAllegory' (α : Type*) [AltAllegory α] : BooleanAllegory' α where
  conv := star
  conv_le_iff_le_conv a b := by
    nth_rw 1 [← sup_eq_left, ← star_involutive b, ← star_sup, star_eq_iff_star_eq, Eq.comm,
      sup_eq_left]
  conv_mul := star_mul
  mul_sup := mul_sup
  mul_bot a := by
    grw [eq_bot_iff, ← compl_top, ← star_mul_compl_le (star a)]
    gcongr <;> simp
  left_modular a b c := by
    nth_grw 1 [← isCompl_compl.le_sup_right_iff_inf_left_le, ← star_mul_compl_le (star a) c,
      star_involutive a, ← mul_sup, sup_comm, ← le_sup_inf, compl_sup_eq_top, inf_top_eq]
    exact mul_right_mono le_sup_right

instance : BooleanAllegory α := @BooleanAllegory.mk' _ (toBooleanAllegory' α)

end AltAllegory
