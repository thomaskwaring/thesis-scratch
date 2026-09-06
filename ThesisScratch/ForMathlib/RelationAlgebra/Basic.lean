
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Order.CompleteBooleanAlgebra

open Relation Function Set

class Allegory (L : Type*) extends SemilatticeInf L, Monoid L, MulLeftMono L where
  conv : L → L
  conv_le_iff_le_conv (x y : L) : conv x ≤ y ↔ x ≤ conv y
  conv_mul (x y : L) : conv (x * y) = conv y * conv x
  left_modular (x y z : L) : x * y ⊓ z ≤ x * (y ⊓ conv x * z)

namespace Allegory

attribute [scoped grind .] le_top bot_le inf_le_left inf_le_right le_sup_left le_sup_right

variable {L : Type*} [Allegory L]

scoped notation:max x "ᵒ" => conv x

lemma conv_conv (x : L) : xᵒᵒ = x :=
  (conv_le_iff_le_conv xᵒ x |>.mpr le_rfl).antisymm (conv_le_iff_le_conv x xᵒ |>.mp le_rfl)

attribute [simp, scoped grind =] conv_conv conv_mul

@[simp, scoped grind =] lemma conv_le_conv_iff (x y : L) : xᵒ ≤ yᵒ ↔ x ≤ y := by
  convert conv_le_iff_le_conv x yᵒ
  simp

lemma conv_eq_conv_iff (x y : L) : xᵒ = yᵒ ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  convert congr_arg conv h <;> simp

@[gcongr]
lemma conv_mono {x y : L} (h : x ≤ y) : xᵒ ≤ yᵒ := (conv_le_conv_iff x y).mpr h

def convIso (L : Type*) [Allegory L] : L ≃o L where
  toFun := conv
  invFun := conv
  map_rel_iff' := conv_le_conv_iff _ _
  left_inv := conv_conv
  right_inv := conv_conv

instance : MulRightMono L where
  elim x y z h := by
    simp only [swap]
    rw [←conv_le_conv_iff, conv_mul, conv_mul]
    exact mul_right_mono (conv_le_conv_iff y z |>.mpr h)

lemma le_mul_top [OrderTop L] (x : L) : x ≤ x * ⊤ := by nth_grw 1 [←mul_one x, le_top (a := 1)]

lemma le_top_mul [OrderTop L] (x : L) : x ≤ ⊤ * x := by nth_grw 1 [←one_mul x, le_top (a := 1)]

@[simp, scoped grind =] lemma conv_inf (x y : L) : (x ⊓ y)ᵒ = xᵒ ⊓ yᵒ := convIso L |>.map_inf x y

@[simp, scoped grind =] lemma conv_one : (1 : L)ᵒ = 1 := by
  have : (1 : L)ᵒ * 1 = 1 := by rw [←conv_conv (1ᵒ * 1), conv_mul]; simp
  simpa using this

@[simp, scoped grind =] lemma conv_bot [OrderBot L] : (⊥ : L)ᵒ = ⊥ := (convIso L).map_bot

@[simp, scoped grind =] lemma conv_top [OrderTop L] : (⊤ : L)ᵒ = ⊤ := (convIso L).map_top

lemma right_modular (x y z : L) : x * y ⊓ z ≤ (x ⊓ z * yᵒ) * y := by
  convert (conv_le_conv_iff _ _).mpr <| left_modular yᵒ xᵒ zᵒ using 1
    <;> simp

lemma inf_mul_le (x y z : L) : (x ⊓ y) * z ≤ x * z ⊓ y * z := by
  apply le_inf <;> apply mul_left_mono
  · exact inf_le_left
  · exact inf_le_right

lemma mul_inf_le (x y z : L) : x * (y ⊓ z) ≤ x * y ⊓ x * z := by
  apply le_inf <;> apply mul_right_mono
  · exact inf_le_left
  · exact inf_le_right

lemma le_mul_mul (x : L) : x ≤ x * xᵒ * x := by
  simpa [mul_assoc] using (left_modular x 1 x).trans (mul_inf_le x 1 (x ᵒ * x))

class UnionAllegory (L : Type*) extends Allegory L, Lattice L, OrderBot L where
  mul_sup (x y z : L) : x * (y ⊔ z) = x * y ⊔ x * z
  mul_bot (x : L) : x * ⊥ = ⊥

open UnionAllegory

section UnionAllegory

attribute [simp, grind =] mul_sup mul_bot

variable {L : Type*} [UnionAllegory L]

@[simp, scoped grind =] lemma conv_sup (x y : L) : (x ⊔ y)ᵒ = xᵒ ⊔ yᵒ := (convIso L).map_sup x y

@[simp, scoped grind =] lemma sup_mul (x y z : L) : (x ⊔ y) * z = x * z ⊔ y * z := by
  rw [←conv_conv ((x ⊔ y) * z), conv_mul]
  simp [mul_sup]

@[simp, scoped grind =] lemma bot_mul (x : L) : ⊥ * x = ⊥ := by
  rw [←le_bot_iff, ←conv_bot, ←conv_le_iff_le_conv]
  simp

end UnionAllegory

class DistribAllegory (L : Type*) extends UnionAllegory L, DistribLattice L

class DivisionAllegory (L : Type*) extends Allegory L where
  over (x y : L) : L
  le_over_iff (x y z : L) : x ≤ over y z ↔ x * z ≤ y

open DivisionAllegory

section DivisionAllegory

variable {L : Type*} [DivisionAllegory L]

scoped infix:60 " // " => over

def under (x y : L) : L := (yᵒ // xᵒ)ᵒ

scoped infix:60 " \\\\ " => under

lemma le_under_iff (x y z : L) : x ≤ y \\ z ↔ y * x ≤ z := by
  rw [under, ←conv_le_iff_le_conv, le_over_iff, ←conv_mul, conv_le_conv_iff]

attribute [simp, grind =] le_over_iff le_under_iff

lemma over_mul_le (x y : L) : (x // y) * y ≤ x := le_over_iff (x // y) x y |>.mp le_rfl

lemma le_over_mul (x y : L) : x ≤ x * y // y := le_over_iff x (x * y) y |>.mpr le_rfl

lemma mul_under_le (x y : L) : x * (x \\ y) ≤ y := le_under_iff (x \\ y) x y |>.mp le_rfl

lemma le_mul_under (x y : L) : y ≤ x \\ (x * y) := le_under_iff y x (x * y) |>.mpr le_rfl

lemma over_under_assoc (x y z : L) : x \\ (y // z) = (x \\ y) // z := by
  apply eq_of_forall_le_iff
  grind

@[simp, scoped grind =] lemma over_one (x : L) : x // 1 = x := by
  apply eq_of_forall_le_iff
  grind

@[simp, scoped grind =] lemma under_one (x : L) : 1 \\ x = x := by
  apply eq_of_forall_le_iff
  grind

@[simp] lemma conv_over (x y : L) : (x // y)ᵒ = yᵒ \\ xᵒ := by
  apply eq_of_forall_le_iff
  simp_rw [le_under_iff, ←conv_le_iff_le_conv]
  grind

@[simp] lemma conv_under (x y : L) : (x \\ y)ᵒ = yᵒ // xᵒ := by
  apply eq_of_forall_le_iff
  simp_rw [le_over_iff, ←conv_le_iff_le_conv]
  simp

@[simp] lemma inf_over (x y z : L) : (x ⊓ y) // z = (x // z) ⊓ (y // z) := by
  apply eq_of_forall_le_iff
  simp

@[simp] lemma under_inf (x y z : L) : x \\ (y ⊓ z) = (x \\ y) ⊓ (x \\ z) := by
  apply eq_of_forall_le_iff
  simp

lemma _root_.IsBot.isTop_under {x : L} (hx : IsBot x) (y : L) : IsTop (x \\ y) := by
  intro z
  simp [le_under_iff, ←le_over_iff, hx (y // z)]

@[simp] lemma bot_under [BoundedOrder L] (x : L) : ⊥ \\ x = ⊤ := (isBot_bot.isTop_under x).eq_top

lemma _root_.IsBot.isTop_over (x : L) {y : L} (hy : IsBot y) : IsTop (x // y) := by
  intro z
  simp [le_over_iff, ←le_under_iff, hy (z \\ x)]

@[simp] lemma over_bot [BoundedOrder L] (x : L) : x // ⊥ = ⊤ := (isBot_bot.isTop_over x).eq_top

@[gcongr] lemma under_mono_right (x : L) {y y' : L} (h : y ≤ y') : x \\ y ≤ x \\ y' := by
  grw [le_under_iff, ←h, mul_under_le]

@[gcongr] lemma over_mono_left {x x' : L} (y : L) (h : x ≤ x') : x // y ≤ x' // y := by
  grw [le_over_iff, ←h, over_mul_le]

@[gcongr] lemma under_anti_left {x x' : L} (y : L) (h : x ≤ x') : x' \\ y ≤ x \\ y := by
  grw [le_under_iff, h, mul_under_le]

@[gcongr] lemma over_anti_right (x : L) {y y' : L} (h : y ≤ y') : x // y' ≤ x // y := by
  grw [le_over_iff, h, over_mul_le]

@[simp] lemma under_under (x y z : L) : x \\ (y \\ z) = y * x \\ z := by
  apply eq_of_forall_le_iff
  simp [mul_assoc]

@[simp] lemma over_over (x y z : L) : (x // y) // z = x // (z * y) := by
  apply eq_of_forall_le_iff
  simp [mul_assoc]

lemma under_top_mul_mul_top [OrderTop L] (x y : L) : (x \\ y * ⊤) * ⊤ = x \\ y * ⊤ := by
  refine le_antisymm ?_ (le_mul_top ..)
  grw [le_under_iff, ←mul_assoc, mul_under_le, mul_assoc, le_top (a := ⊤ * ⊤)]

lemma top_mul_mul_top_over [OrderTop L] (x y : L) : ⊤ * (⊤ * x // y) = ⊤ * x // y := by
  refine le_antisymm ?_ (le_top_mul ..)
  grw [le_over_iff, mul_assoc, over_mul_le, ←mul_assoc, le_top (a := ⊤ * ⊤)]

end DivisionAllegory

class UnionDivAllegory (L : Type*) extends DivisionAllegory L, Lattice L, BoundedOrder L

section UnionDivAllegory

variable {L : Type*} [UnionDivAllegory L]

instance : UnionAllegory L where
  mul_sup x y z := by
    apply eq_of_forall_ge_iff
    simp_rw [←le_under_iff, sup_le_iff, le_under_iff]
    simp
  mul_bot x := IsBot.eq_bot <| by simp [IsBot, ←le_under_iff]

@[simp] lemma over_sup (x y z : L) : x // (y ⊔ z) = (x // y) ⊓ (x // z) := by
  apply eq_of_forall_le_iff
  simp

@[simp] lemma sup_under (x y z : L) : (x ⊔ y) \\ z = (x \\ z) ⊓ (y \\ z) := by
  apply eq_of_forall_le_iff
  simp

lemma sup_over_ge (x y z : L) : (x // z) ⊔ (y // z) ≤ (x ⊔ y) // z :=
  sup_le (over_mono_left z le_sup_left) (over_mono_left z le_sup_right)

lemma under_sup_ge (x y z : L) : (x \\ y) ⊔ (x \\ z) ≤ x \\ (y ⊔ z) :=
  sup_le (under_mono_right x le_sup_left) (under_mono_right x le_sup_right)

end UnionDivAllegory

class BooleanAllegory' (L : Type*) extends UnionAllegory L, BooleanAlgebra L

@[simp, scoped grind =] lemma conv_compl {L : Type*} [BooleanAllegory' L] (x : L) : xᶜᵒ = xᵒᶜ := by
  rw [eq_compl_iff_isCompl]
  exact convIso L |>.isCompl isCompl_compl.symm

lemma mul_le_compl_iff {L : Type*} [BooleanAllegory' L] (x y z : L) :
    x * y ≤ zᶜ ↔ xᵒ * z ≤ yᶜ := by
  have h (a b c : L) (h : a * b ≤ cᶜ) : aᵒ * c ≤ bᶜ := by
    calc
    aᵒ * c = aᵒ * c ⊓ (b ⊔ bᶜ) := by simp
    _ ≤ aᵒ * c ⊓ b ⊔ bᶜ := by rw [inf_sup_left]; gcongr; grind
    _ ≤ aᵒ * (c ⊓ a * b) ⊔ bᶜ := by convert sup_le_sup_right (left_modular aᵒ c b) bᶜ using 1; simp
    _ ≤ aᵒ * (c ⊓ cᶜ) ⊔ bᶜ := by gcongr
    _ = bᶜ := by simp
  refine ⟨h x y z, ?_⟩
  convert h xᵒ z y
  simp

lemma mul_le_compl_iff' {L : Type*} [BooleanAllegory' L] (x y z : L) :
    x * y ≤ zᶜ ↔ z * yᵒ ≤ xᶜ := by
  rw [←conv_le_conv_iff, conv_mul, conv_compl, mul_le_compl_iff, ←conv_mul, ←conv_compl,
    conv_le_conv_iff]

class BooleanAllegory (L : Type*) extends UnionDivAllegory L, BooleanAlgebra L

@[implicit_reducible]
protected def BooleanAllegory.mk' (L : Type*) [BooleanAllegory' L] : BooleanAllegory L where
  over x y := (xᶜ * yᵒ)ᶜ
  le_over_iff x y z := by rw [le_compl_comm (a := x) (b := yᶜ * zᵒ), ←mul_le_compl_iff',
    compl_compl]

section BooleanAllegory

variable {L : Type*} [BooleanAllegory L]

instance : BooleanAllegory' L where

instance : DistribAllegory L where

theorem mul_le_compl_tfae (x y z : L) :
    [x * y ≤ zᶜ, xᵒ * z ≤ yᶜ, z * yᵒ ≤ xᶜ].TFAE := by
  tfae_have 1 ↔ 2 := mul_le_compl_iff x y z
  tfae_have 1 ↔ 3 := mul_le_compl_iff' x y z
  tfae_finish

lemma conv_mul_compl_mul_le_compl (x y : L) : xᵒ * (x * y)ᶜ ≤ yᶜ := by
  rw [←mul_le_compl_iff, compl_compl]

lemma over_eq (x y : L) : x // y = (xᶜ * yᵒ)ᶜ := by
  apply eq_of_forall_le_iff
  intro z
  rw [le_compl_comm, ←mul_le_compl_iff', compl_compl, le_over_iff]

lemma under_eq (x y : L) : x \\ y = (xᵒ * yᶜ)ᶜ := by
  rw [under, over_eq]
  simp

end BooleanAllegory

class CompleteAllegory (L : Type*) extends DivisionAllegory L, CompleteLattice L

section CompleteAllegory

variable {L : Type*} [CompleteAllegory L]

lemma mul_sSup (x : L) (ys : Set L) : x * sSup ys = ⨆ y ∈ ys, x * y := by
  apply eq_of_forall_ge_iff
  intro z
  simp_rw [iSup_le_iff, ←le_under_iff, sSup_le_iff]

lemma sSup_mul (xs : Set L) (y : L) : sSup xs * y = ⨆ x ∈ xs, x * y := by
  apply eq_of_forall_ge_iff
  intro z
  simp_rw [iSup_le_iff, ←le_over_iff, sSup_le_iff]

lemma conv_sSup (xs : Set L) : (sSup xs)ᵒ = ⨆ x ∈ xs, xᵒ := convIso L |>.map_sSup xs

instance : UnionDivAllegory L where

end CompleteAllegory

class CompleteAllegory' (L : Type*) extends Allegory L, CompleteLattice L where
  sSup_mul' (xs : Set L) (y : L) : sSup xs * y = ⨆ x ∈ xs, x * y

section CompleteAllegory'

variable {L : Type*} [CompleteAllegory' L]

instance : CompleteAllegory L where
  over x y := sSup {z | z * y ≤ x}
  le_over_iff x y z := by
    refine ⟨fun h => (mul_left_mono h).trans ?_, fun h => le_sSup h⟩
    simp [CompleteAllegory'.sSup_mul']

end CompleteAllegory'

class RelationAlgebra (L : Type*) extends BooleanAllegory L, CompleteBooleanAlgebra L

instance (L : Type*) [RelationAlgebra L] : CompleteAllegory L where

end Allegory
