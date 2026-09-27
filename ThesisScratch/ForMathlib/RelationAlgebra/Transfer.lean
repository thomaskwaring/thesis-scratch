import ThesisScratch.ForMathlib.RelationAlgebra.Basic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Submonoid.Defs

open Allegory

abbrev Function.Injective.allegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [LE L₁] [LT L₁] [Allegory L₂] {f : L₁ → L₂} (hf : Function.Injective f) (conv : L₁ → L₁)
    (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x) (lt : ∀ {x y : L₁}, f y < f x ↔ y < x)
    (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b)
    (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ) : Allegory L₁ where
  __ := hf.semilatticeInf f le lt @map_inf
  __ := hf.monoid f one @mul @npow
  elim _ _ _ h := by simpa [← le, mul] using mul_right_mono (le.mpr h)
  conv := conv
  conv_le_iff_le_conv := by simp [← le, map_conv, conv_le_iff_le_conv]
  conv_mul _ _ := hf <| by simp [map_conv, mul]
  left_modular x y z := by simpa [← le, mul, map_inf, map_conv] using left_modular (f x) (f y) (f z)

-- require `f ⊥ = ⊥` rather than `OrderBot L₁` for the `mul_bot` axiom.
abbrev Function.Injective.unionAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [Max L₁] [Bot L₁] [LE L₁] [LT L₁] [UnionAllegory L₂] {f : L₁ → L₂} (hf : Function.Injective f)
    (conv : L₁ → L₁) (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x) (lt : ∀ {x y : L₁}, f y < f x ↔ y < x)
    (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b) (map_sup : ∀ {a b : L₁}, f (a ⊔ b) = f a ⊔ f b)
    (map_bot : f ⊥ = ⊥) (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ) : UnionAllegory L₁ where
  __ := hf.lattice f le lt @map_sup @map_inf
  __ := hf.allegory conv le lt map_inf one mul npow map_conv
  bot_le _ := le.mp <| map_bot ▸ bot_le
  mul_sup _ _ _ := hf <| by simp [mul, map_sup]
  mul_bot _ := hf <| by simp [mul, map_bot]

abbrev Function.Injective.distribAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [Max L₁] [Bot L₁] [LE L₁] [LT L₁] [DistribAllegory L₂] {f : L₁ → L₂} (hf : Function.Injective f)
    (conv : L₁ → L₁) (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x) (lt : ∀ {x y : L₁}, f y < f x ↔ y < x)
    (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b) (map_sup : ∀ {a b : L₁}, f (a ⊔ b) = f a ⊔ f b)
    (map_bot : f ⊥ = ⊥) (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ) : DistribAllegory L₁ where
  __ := hf.unionAllegory conv le lt map_inf map_sup map_bot one mul npow map_conv
  __ := hf.distribLattice f le lt @map_sup @map_inf

-- require `f ⊥ = ⊥` rather than `OrderBot L₁` for the `mul_bot` axiom.
abbrev Function.Injective.divisionAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [LE L₁] [LT L₁] [DivisionAllegory L₂] {f : L₁ → L₂} (hf : Function.Injective f) (conv : L₁ → L₁)
    (over : L₁ → L₁ → L₁) (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x)
    (lt : ∀ {x y : L₁}, f y < f x ↔ y < x) (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b)
    (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ)
    (map_over : ∀ {x y : L₁}, f (over x y) = f x // f y) : DivisionAllegory L₁ where
  __ := hf.semilatticeInf f le lt @map_inf
  __ := hf.allegory conv le lt map_inf one mul npow map_conv
  over := over
  le_over_iff := by simp [← le, map_over, mul]

abbrev Function.Injective.unionDivAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [Max L₁] [Bot L₁] [LE L₁] [LT L₁] [OrderTop L₁] [UnionDivAllegory L₂] {f : L₁ → L₂}
    (hf : Function.Injective f) (conv : L₁ → L₁) (over : L₁ → L₁ → L₁)
    (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x) (lt : ∀ {x y : L₁}, f y < f x ↔ y < x)
    (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b) (map_sup : ∀ {a b : L₁}, f (a ⊔ b) = f a ⊔ f b)
    (map_bot : f ⊥ = ⊥) (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ)
    (map_over : ∀ {x y : L₁}, f (over x y) = f x // f y) : UnionDivAllegory L₁ where
  __ := hf.divisionAllegory conv over le lt map_inf one mul npow map_conv map_over
  __ := hf.lattice f le lt @map_sup @map_inf
  le_top _ := le_top
  bot_le _ := le.mp <| map_bot ▸ bot_le

abbrev Function.Injective.booleanAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Min L₁]
    [Max L₁] [SDiff L₁] [Bot L₁] [LE L₁] [LT L₁] [OrderTop L₁] [BooleanAllegory L₂] {f : L₁ → L₂}
    (hf : Function.Injective f) (conv : L₁ → L₁) (over : L₁ → L₁ → L₁)
    (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x) (lt : ∀ {x y : L₁}, f y < f x ↔ y < x)
    (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b) (map_sup : ∀ {a b : L₁}, f (a ⊔ b) = f a ⊔ f b)
    (map_sdiff : ∀ {a b : L₁}, f (a \ b) = f a \ f b) (map_bot : f ⊥ = ⊥) (one : f 1 = 1)
    (mul : ∀ {x y : L₁}, f (x * y) = f x * f y) (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ)
    (map_over : ∀ {x y : L₁}, f (over x y) = f x // f y) : BooleanAllegory L₁ where
  __ := hf.unionDivAllegory conv over le lt map_inf map_sup map_bot one mul npow map_conv map_over
  __ := @GeneralizedBooleanAlgebra.toBooleanAlgebra L₁
    (hf.generalizedBooleanAlgebra f le lt @map_sup @map_inf map_bot @map_sdiff ) _

abbrev Function.Injective.completeAllegory {L₁ L₂ : Type*} [Mul L₁] [One L₁] [Pow L₁ ℕ] [Max L₁]
    [Min L₁] [LE L₁] [LT L₁] [SupSet L₁] [InfSet L₁] [OrderTop L₁] [Bot L₁] [CompleteAllegory L₂]
    {f : L₁ → L₂} (hf : Function.Injective f) (conv : L₁ → L₁)
    (over : L₁ → L₁ → L₁) (le : ∀ {x y : L₁}, f y ≤ f x ↔ y ≤ x)
    (lt : ∀ {x y : L₁}, f y < f x ↔ y < x) (map_inf : ∀ {a b : L₁}, f (a ⊓ b) = f a ⊓ f b)
    (map_sup : ∀ {a b : L₁}, f (a ⊔ b) = f a ⊔ f b) (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a)
    (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) (map_bot : f ⊥ = ⊥)
    (one : f 1 = 1) (mul : ∀ {x y : L₁}, f (x * y) = f x * f y)
    (npow : ∀ {x : L₁} {n : ℕ}, f (x ^ n) = f x ^ n)
    (map_conv : ∀ {x : L₁}, f (conv x) = (f x)ᵒ)
    (map_over : ∀ {x y : L₁}, f (over x y) = f x // f y) : CompleteAllegory L₁ where
  __ := hf.unionDivAllegory conv over le lt map_inf map_sup map_bot one mul npow map_conv map_over
  isLUB_sSup s := .of_image le <| by rw [map_sSup]; exact isLUB_biSup
  isGLB_sInf s := .of_image le <| by rw [map_sInf]; exact isGLB_biInf

namespace Allegory

structure Suballegory (L : Type*) [Allegory L] extends Submonoid L where
  inf_mem' {x y : L} : x ∈ carrier → y ∈ carrier → x ⊓ y ∈ carrier
  conv_mem' {x : L} : x ∈ carrier → xᵒ ∈ carrier

namespace Suballegory

variable {L : Type*} [Allegory L]

lemma toSubmonoid_injective : (Suballegory.toSubmonoid (L := L)).Injective := by
  intro M M' h
  cases M; cases M'
  congr

instance : SetLike (Suballegory L) L where
  coe M := M.carrier
  coe_injective := SetLike.coe_injective.comp toSubmonoid_injective

variable {M : Suballegory L}

@[simp] lemma mem_carrier {x : L} : x ∈ M.carrier ↔ x ∈ M := Iff.rfl

-- coe / mk lemmas

lemma mul_mem {x y : L} (hx : x ∈ M) (hy : y ∈ M) : x * y ∈ M := M.mul_mem' hx hy

lemma one_mem : (1 : L) ∈ M := M.one_mem'

lemma inf_mem {x y : L} (hx : x ∈ M) (hy : y ∈ M) : x ⊓ y ∈ M := M.inf_mem' hx hy

lemma conv_mem {x : L} (hx : x ∈ M) : xᵒ ∈ M := M.conv_mem' hx

instance : Monoid M := inferInstanceAs (Monoid M.toSubmonoid)

instance : SemilatticeInf M := Subtype.semilatticeInf (fun _ _ => M.inf_mem)

instance : Allegory M :=
  Subtype.coe_injective.allegory (fun x => ⟨(x : L)ᵒ, M.conv_mem' x.property⟩)
    .rfl .rfl rfl rfl rfl rfl rfl

@[simp, norm_cast] lemma coe_mul (x y : M) : x * y = (x : L) * y := rfl

@[simp, norm_cast] lemma coe_one : ((1 : M) : L) = 1 := rfl

@[simp, norm_cast] lemma coe_inf (x y : M) : x ⊓ y = (x : L) ⊓ y := rfl

@[simp, norm_cast] lemma coe_conv (x : M) : xᵒ = (x : L)ᵒ := rfl

end Suballegory

end Allegory
