import ThesisScratch.ForMathlib.RelationAlgebra.Basic
import Mathlib.Order.FixedPoints

namespace Allegory

variable {L : Type*} [Allegory L]

open UnionAllegory DivisionAllegory OrderHom

section Properties

class AllRefl (x : L) : Prop where
  one_le' : 1 ≤ x

@[scoped grind .]
lemma one_le' (x : L) [AllRefl x] : 1 ≤ x := AllRefl.one_le'

lemma mul_right_ge (x y : L) [AllRefl y] : x ≤ x * y :=
  (mul_one x).ge.trans (mul_right_mono (one_le' y))

lemma mul_left_ge (x y : L) [AllRefl y] : x ≤ y * x :=
  (one_mul x).ge.trans (mul_left_mono <| one_le' y)

lemma allRefl_of_ge {x y : L} (h : x ≤ y) [AllRefl x] : AllRefl y := ⟨(one_le' x).trans h⟩

instance {x : L} [AllRefl x] : AllRefl xᵒ where
  one_le' := by
    rw [←conv_le_iff_le_conv, conv_one]
    exact one_le' x

instance allRefl_top [OrderTop L] : AllRefl (⊤ : L) := ⟨le_top⟩

instance allRefl_one : AllRefl (1 : L) := ⟨le_rfl⟩

instance allRefl_mul (x y : L) [AllRefl x] [AllRefl y] : AllRefl (x * y) where
  one_le' := by nth_grw 1 [one_le' x, mul_right_ge x y]

class AllSymm (x : L) : Prop where
  conv_eq : xᵒ = x

@[simp, scoped grind =] lemma conv_eq (x : L) [AllSymm x] : xᵒ = x := AllSymm.conv_eq

lemma allSymm_of_le_conv {x : L} (h : x ≤ xᵒ) : AllSymm x :=
  ⟨(conv_le_iff_le_conv x x |>.mpr h).antisymm h⟩

lemma allSymm_of_conv_le {x : L} (h : xᵒ ≤ x) : AllSymm x :=
  ⟨h.antisymm <| conv_le_iff_le_conv x x |>.mp h⟩

instance {x : L} [AllSymm x] : AllSymm xᵒ where
  conv_eq := by rw [conv_eq x]; exact conv_eq x

instance allSymm_top [OrderTop L] : AllSymm (⊤ : L) := ⟨conv_top⟩

instance allSymm_one : AllSymm (1 : L) := ⟨conv_one⟩

instance allSymm_bot [OrderBot L] : AllSymm (⊥ : L) := ⟨conv_bot⟩

instance {x y : L} [AllSymm x] [AllSymm y] : AllSymm (x ⊓ y) where
  conv_eq := by
    rw [conv_inf, conv_eq, conv_eq]

instance {L : Type*} [UnionAllegory L] {x y : L} [AllSymm x] [AllSymm y] :
    AllSymm (x ⊔ y) where
  conv_eq := by rw [conv_sup x y, conv_eq, conv_eq]

class AllTrans (x : L) : Prop where
  mul_self_le : x * x ≤ x

@[scoped grind →] lemma mul_self_le (x : L) [AllTrans x] : x * x ≤ x := AllTrans.mul_self_le

instance {x : L} [AllTrans x] : AllTrans xᵒ where
  mul_self_le := by rw [←conv_mul, conv_le_conv_iff]; exact mul_self_le x

instance allTrans_top [OrderTop L] : AllTrans (⊤ : L) := ⟨le_top⟩

instance allTrans_one : AllTrans (1 : L) := ⟨(one_mul 1).le⟩

instance allTrans_bot {L : Type*} [UnionAllegory L] : AllTrans (⊥ : L) := ⟨(bot_mul ⊥).le⟩

instance allTrans_inf {x y : L} [AllTrans x] [AllTrans y] : AllTrans (x ⊓ y) where
  mul_self_le := calc
    (x ⊓ y) * (x ⊓ y) ≤ x * (x ⊓ y) ⊓ y * (x ⊓ y) := inf_mul_le x y (x ⊓ y)
    _ ≤ x * x ⊓ y * y := inf_le_inf (mul_right_mono inf_le_left) (mul_right_mono inf_le_right)
    _ ≤ x ⊓ y := inf_le_inf (mul_self_le x) (mul_self_le y)

@[simp] lemma eq_mul_self (x : L) [AllRefl x] [AllTrans x] : x * x = x :=
  (mul_self_le x).antisymm (mul_left_ge x x)

@[simp] lemma mul_right_idem (x y : L) [AllRefl y] [AllTrans y] : x * y * y = x * y := by
  rw [mul_assoc, eq_mul_self]

@[simp] lemma mul_left_idem (x y : L) [AllRefl x] [AllTrans x] : x * (x * y) = x * y := by
  rw [←mul_assoc, eq_mul_self]

section Monad

variable {L : Type*} [DivisionAllegory L]

instance allRefl_over_self (x : L) : AllRefl (x // x) where
  one_le' := by rw [le_over_iff, one_mul]

instance allRefl_under_self (x : L) : AllRefl (x \\ x) where
  one_le' := by rw [le_under_iff, mul_one]

instance allTrans_over_self (x : L) : AllTrans (x // x) where
  mul_self_le := by
    rw [le_over_iff, mul_assoc]
    exact mul_right_mono (over_mul_le x x) |>.trans (over_mul_le x x)

instance allTrans_under_self (x : L) : AllTrans (x \\ x) where
  mul_self_le := by
    rw [le_under_iff, ←mul_assoc]
    exact mul_left_mono (mul_under_le x x) |>.trans (mul_under_le x x)

end Monad

end Properties

section Closure

variable {L : Type*} [UnionAllegory L]

@[reducible] def reflGen (x : L) := x ⊔ 1

notation:max x "⁼" => reflGen x

instance (x : L) : AllRefl x⁼ := ⟨le_sup_right⟩

@[simp] lemma conv_reflGen (x : L) : x⁼ᵒ = xᵒ⁼ := by simp

@[simp] lemma reflGen_inf {L : Type*} [DistribAllegory L] (x y : L) : (x ⊓ y)⁼ = x⁼ ⊓ y⁼ := by
  simp_rw [reflGen, sup_inf_right]

@[simp] lemma reflGen_sup (x y : L) : (x ⊔ y)⁼ = x⁼ ⊔ y⁼ := by grind

@[gcongr] lemma reflGen_mono {x y : L} (h : x ≤ y) : x⁼ ≤ y⁼ := sup_le_sup_right h 1

@[simp] lemma reflGen_bot : (⊥ : L)⁼ = 1 := by simp

@[simp] lemma reflGen_allRefl (x : L) [AllRefl x] : x⁼ = x := sup_eq_left.mpr (one_le' x)

@[simp] lemma reflGen_le (x y : L) [AllRefl y] : x⁼ ≤ y ↔ x ≤ y := by simp [one_le' y]

lemma le_reflGen (x : L) : x ≤ x⁼ := le_sup_left

instance (x : L) [AllSymm x] : AllSymm x⁼ := inferInstance

instance (x : L) [AllTrans x] : AllTrans x⁼ where
  mul_self_le := by
    simp only [reflGen, mul_sup, sup_mul, one_mul, mul_one, sup_le_iff, le_sup_left,
      and_true, Std.le_refl]
    exact (mul_self_le x).trans le_sup_left

@[reducible] def symmGen (x : L) := x ⊔ xᵒ

notation:max x "ˢ" => symmGen x

instance (x : L) : AllSymm xˢ := ⟨by simp [sup_comm]⟩

@[simp] lemma symmGen_conv (x : L) : xᵒˢ = xˢ := by simp [symmGen, sup_comm]

@[simp] lemma symmGen_sup (x y : L) : (x ⊔ y)ˢ = xˢ ⊔ yˢ := by grind

@[gcongr] lemma symmGen_mono {x y : L} (h : x ≤ y) : xˢ ≤ yˢ := by simp_rw [symmGen]; gcongr

@[simp] lemma symmGen_allSymm (x : L) [AllSymm x] : xˢ = x := by simp

@[simp] lemma symmGen_le_iff (x y : L) [AllSymm y] : xˢ ≤ y ↔ x ≤ y := by
  simp only [sup_le_iff, and_iff_left_iff_imp, conv_le_iff_le_conv, conv_eq y]
  exact id

lemma le_symmGen (x : L) : x ≤ xˢ := le_sup_left

lemma conv_le_symmGen (x : L) : xᵒ ≤ xˢ := le_sup_right

instance (x : L) [AllRefl x] : AllRefl xˢ := ⟨(one_le' x).trans le_sup_left⟩

variable {L : Type*} [CompleteAllegory L]

@[simps]
def stepFun (x : L) : L →o L where
  toFun y := x ⊔ x * y
  monotone' x y h := by simp only; gcongr

def transGen (x : L) := (stepFun x).lfp

notation:max x "⁺" => transGen x

lemma le_transGen (x : L) : x ≤ x⁺ := by
  rw [transGen, ←map_lfp]
  simp [-map_lfp]

lemma mul_transGen_le_transGen (x : L) : x * x⁺ ≤ x⁺ := by
  rw [transGen]
  nth_rw 2 [←map_lfp]
  simp [stepFun_coe, -map_lfp]

@[gcongr] lemma transGen_mono {x y : L} (h : x ≤ y) : x⁺ ≤ y⁺ :=
  lfp.mono fun z => by
    rw [stepFun_coe, stepFun_coe]
    gcongr

lemma transGen_induction (p : L → Prop) (x : L) (hx : p x) (hstep : ∀ y ≤ x⁺, p y → p (x * y))
    (hsup : ∀ s, (∀ y ∈ s, p y) → p (sSup s)) : p x⁺ := by
  refine (stepFun x).lfp_induction ?_ hsup
  intro y hy hy'
  rw [stepFun_coe, ←sSup_pair]
  apply hsup
  simpa [hx] using hstep y hy' hy

instance (x : L) : AllTrans x⁺ where
  mul_self_le := by
    apply transGen_induction (· * x⁺ ≤ x⁺) x (mul_transGen_le_transGen x)
    · intro y hy hy'
      grw [mul_assoc, hy', mul_transGen_le_transGen]
    · intro s hs
      simp_rw [←le_over_iff, sSup_le_iff, le_over_iff]
      assumption

lemma transGen_le (x y : L) [AllTrans y] : x⁺ ≤ y ↔ x ≤ y := by
  refine ⟨(le_transGen x).trans, fun h => ?_⟩
  apply transGen_induction (· ≤ y) x h
  · intro z _ hz
    grw [h, hz, mul_self_le y]
  · simp

@[simp] lemma transGen_allTrans (x : L) [AllTrans x] : x⁺ = x :=
  (transGen_le x x |>.mpr le_rfl).antisymm (le_transGen x)

@[simp] lemma conv_transGen (x : L) : x⁺ᵒ = xᵒ⁺ := by
  suffices ∀ z : L, zᵒ⁺ ≤ z⁺ᵒ by
    refine le_antisymm ?_ (this x)
    nth_grw 1 [←conv_conv x, this xᵒ, conv_conv]
  intro x
  rw [transGen_le, conv_le_conv_iff]
  exact le_transGen x

lemma transGen_mul_le_transGen (x : L) : x⁺ * x ≤ x⁺ := by
  rw [←conv_le_conv_iff, conv_mul, conv_transGen]
  exact mul_transGen_le_transGen xᵒ

lemma transGen_mul_eq_mul_transGen (x : L) : x⁺ * x = x * x⁺ := by
  suffices ∀ y, y⁺ * y ≤ y * y⁺ by
    refine (this x).antisymm ?_
    rw [←conv_le_conv_iff, conv_mul, conv_mul, conv_transGen]
    exact this xᵒ
  intro y
  apply transGen_induction (· * y ≤ y * y⁺) y (mul_right_mono <| le_transGen y)
  · intro x h h'
    nth_grewrite 2 [le_transGen y]
    grw [h, mul_assoc, mul_self_le]
  · intro s h
    simpa [sSup_mul]

lemma transGen_eq_sup (x : L) : x ⊔ x * x⁺ = x⁺ := (stepFun x).map_lfp

lemma transGen_eq_sup' (x : L) : x ⊔ x⁺ * x = x⁺ := by
  convert transGen_eq_sup x using 2
  exact transGen_mul_eq_mul_transGen x

instance (x : L) [AllRefl x] : AllRefl x⁺ := ⟨(one_le' x).trans (le_transGen x)⟩

instance (x : L) [AllSymm x] : AllSymm x⁺ := ⟨by simp⟩

lemma symmGen_reflGen (x : L) : x⁼ˢ = xˢ⁼ := by simp

lemma transGen_reflGen (x : L) : x⁼⁺ = x⁺⁼ :=
  (transGen_le _ _).mpr (reflGen_mono (le_transGen x)) |>.antisymm <|
    (reflGen_le _ _).mpr (transGen_mono (le_reflGen x))

def reflTransGen (x : L) : L := x⁺⁼

notation:max x "⋆" => reflTransGen x

lemma reflTransGen_eq_transGen_reflGen (x : L) : x⋆ = x⁼⁺ := transGen_reflGen x |>.symm

lemma reflTransGen_eq_reflGen_transGen (x : L) : x⋆ = x⁺⁼ := rfl

instance (x : L) : AllRefl x⋆ := inferInstanceAs <| AllRefl x⁺⁼

instance (x : L) : AllTrans x⋆ := by rw [reflTransGen_eq_transGen_reflGen]; infer_instance

lemma reflTransGen_induction (p : L → Prop) (x : L) (hone : p 1)
    (hstep : ∀ y ≤ x⋆, p y → p (x * y))
    (hsup : ∀ (s : Set L), (∀ y ∈ s, p y) → p (sSup s)) : p x⋆ := by
  rw [reflTransGen_eq_reflGen_transGen, reflGen, ←sSup_pair]
  suffices p x⁺ by grind
  refine transGen_induction p x ?_ ?_ hsup
  · rw [←mul_one x]
    exact hstep 1 (one_le' x⋆) hone
  · intro y hy hy'
    apply hstep y (hy.trans <| le_reflGen x⁺) hy'

lemma le_reflTransGen (x : L) : x ≤ x⋆ := (le_transGen x).trans <| le_reflGen x⁺

lemma reflTransGen_le (x y : L) [AllRefl y] [AllTrans y] : x⋆ ≤ y ↔ x ≤ y := by
  rw [reflTransGen_eq_transGen_reflGen, transGen_le, reflGen_le]

lemma reflTransGen_le' {x y : L} (h : x * y ≤ y) [AllRefl y] : x⋆ ≤ y := by
  refine reflTransGen_induction (· ≤ y) x (one_le' y) ?_ (by simp)
  intro z hz hz'
  grw [hz', h]

@[gcongr] lemma reflTransGen_mono {x y : L} (h : x ≤ y) : x⋆ ≤ y⋆ := by
  exact reflGen_mono <| transGen_mono h

@[simp] lemma reflTransGen_conv (x : L) : x⋆ᵒ = xᵒ⋆ := by
  simp [reflTransGen]

lemma reflTransGen_induction' (p : L → Prop) (x : L) (hone : p 1)
    (hstep : ∀ y ≤ x⋆, p y → p (y * x))
    (hsup : ∀ (s : Set L), (∀ y ∈ s, p y) → p (sSup s)) : p x⋆ := by
  rw [←conv_conv x, ←reflTransGen_conv]
  apply reflTransGen_induction (p ·ᵒ) xᵒ (by simpa)
  · intro y hy hy'
    simpa using hstep yᵒ (by rwa [conv_le_iff_le_conv, reflTransGen_conv]) hy'
  · intro s hs
    rw [conv_sSup, ←sSup_image]
    apply hsup
    rintro _ ⟨y, hy, rfl⟩
    exact hs y hy

lemma reflTransGen_eq_sup (x : L) : 1 ⊔ x * x⋆ = x⋆ := by
  nth_rw 1 [reflTransGen, reflGen, Eq.comm, reflTransGen, reflGen, ←transGen_eq_sup, ←mul_one x,
    ←mul_sup, sup_comm]
  nth_rw 2 [sup_comm]

lemma reflTransGen_eq_sup' (x : L) : 1 ⊔ x⋆ * x = x⋆ := by
  rw [←conv_eq_conv_iff, conv_sup, conv_mul, reflTransGen_conv, conv_one]
  exact reflTransGen_eq_sup xᵒ

lemma mul_reflTransGen_le_reflTransGen (x : L) : x * x⋆ ≤ x⋆ := by
  nth_grw 1 [le_reflTransGen x, mul_self_le]

lemma reflTransGen_mul_le_reflTransGen (x : L) : x⋆ * x ≤ x⋆ := by
  rw [←conv_le_conv_iff, conv_mul, reflTransGen_conv]
  exact mul_reflTransGen_le_reflTransGen xᵒ

end Closure

section Confluence

variable {L : Type*} [CompleteAllegory L]

abbrev WeaklyCommute (x y : L) : Prop := x * y ≤ y * x

lemma WeaklyCommute.mul_le_mul {x y : L} (h : WeaklyCommute x y) : x * y ≤ y * x := h

lemma WeaklyCommute.conv_swap {x y : L} (h : WeaklyCommute x y) : WeaklyCommute yᵒ xᵒ := by
  rw [WeaklyCommute, ←conv_le_conv_iff]
  simpa

lemma WeaklyCommute.reflTransGen_left {x y : L} (h : WeaklyCommute x y) : WeaklyCommute x⋆ y := by
  refine reflTransGen_induction (· * y ≤ y * x⋆) x (by simpa using mul_right_ge ..) ?_
    (by simp [sSup_mul])
  intro z hz hz'
  grw [mul_assoc, hz', ←mul_assoc, h.mul_le_mul, mul_assoc, mul_reflTransGen_le_reflTransGen]

lemma WeaklyCommute.reflTransGen_right {x y : L} (h : WeaklyCommute x y) : WeaklyCommute x y⋆ := by
  convert h.conv_swap.reflTransGen_left.conv_swap using 1
  all_goals simp

lemma WeaklyCommute.reflTransGen_reflTransGen {x y : L} (h : WeaklyCommute x y) :
    WeaklyCommute x⋆ y⋆ := h.reflTransGen_left.reflTransGen_right

lemma WeaklyCommute.reflTransGen_sup_eq_of_reflTransGen {x y : L} (h : WeaklyCommute x⋆ y⋆) :
    (x ⊔ y)⋆ = y⋆ * x⋆ := by
  apply le_antisymm
  · have : AllTrans (y⋆ * x⋆) := by
      constructor
      nth_grw 1 [show y⋆ * x⋆ * (y⋆ * x⋆) = y⋆ * (x⋆ * y⋆) * x⋆ by simp [mul_assoc], h.mul_le_mul,
        ←mul_assoc, eq_mul_self, mul_assoc, eq_mul_self]
    nth_grw 1 [reflTransGen_le, sup_le_iff, le_reflTransGen x, mul_left_ge x⋆ y⋆]
    simp only [Std.le_refl, true_and]
    nth_grw 1 [le_reflTransGen y, mul_right_ge y⋆ x⋆]
  · rw [←eq_mul_self (x ⊔ y)⋆]
    gcongr <;> simp

lemma weaklyCommute_of_reflTransGen_sup_eq {x y : L} (h : (x ⊔ y)⋆ = y⋆ * x⋆) :
    WeaklyCommute x⋆ y⋆ := by
  rw [WeaklyCommute, ←le_over_iff]
  have : AllRefl (y⋆ * x⋆ // y⋆) := ⟨by nth_grw 1 [le_over_iff, one_mul, mul_right_ge y⋆ x⋆]⟩
  apply reflTransGen_le'
  nth_grw 1 [le_over_iff, mul_assoc, over_mul_le, ←h, ←h, le_sup_left (a := x) (b := y),
      le_reflTransGen (x ⊔ y), mul_self_le]

theorem churchRosser_iff_confluent (x : L) :
    xᵒ⋆ * x⋆ ≤ x⋆ * xᵒ⋆ ↔ xˢ⋆ = x⋆ * xᵒ⋆ := by
  constructor
  · intro (h : WeaklyCommute xᵒ⋆ x⋆)
    convert h.reflTransGen_sup_eq_of_reflTransGen using 1
    rw [symmGen, sup_comm]
  · intro h
    rw [symmGen, sup_comm] at h
    exact weaklyCommute_of_reflTransGen_sup_eq h

end Confluence

end Allegory
