import ThesisScratch.ForMathlib.RelationAlgebra.Properties

open Relation Function Set Allegory UnionAllegory DivisionAllegory

namespace Allegory

variable {L : Type*} [Allegory L]

class AllSet (x : L) : Prop where
  le_one : x ≤ 1

@[grind .]
lemma le_one (x : L) [AllSet x] : x ≤ 1 := AllSet.le_one

@[grind =>]
lemma mul_left_le (x y : L) [AllSet x] : x * y ≤ y := by
  convert mul_left_mono (le_one x)
  simp

@[grind =>]
lemma mul_right_le (x y : L) [AllSet y] : x * y ≤ x := by
  convert mul_right_mono (le_one y)
  simp

instance (x : L) [AllSet x] : AllSet xᵒ where
  le_one := by rw [conv_le_iff_le_conv, conv_one]; exact le_one x

instance (x y : L) [AllSet x] : AllSet (x ⊓ y) where
  le_one := inf_le_left.trans (le_one x)

instance (x y : L) [AllSet y] : AllSet (x ⊓ y) where
  le_one := inf_le_right.trans (le_one y)

instance (x y : L) [AllSet x] [AllSet y] : AllSet (x * y) where
  le_one := mul_right_le x y |>.trans (le_one x)

instance {L : Type*} [UnionAllegory L] (x y : L) [AllSet x] [AllSet y] : AllSet (x ⊔ y) where
  le_one := sup_le (le_one x) (le_one y)

instance : AllSet (1 : L) := ⟨le_rfl⟩

-- instance [OrderBot L] : AllSet (⊥ : L) := ⟩

instance (x : L) [AllSet x] : AllSymm x :=
  allSymm_of_le_conv <| (le_mul_mul x).trans <| (mul_right_le (x * xᵒ) x).trans (mul_left_le x xᵒ)

instance (x : L) [AllSet x] : AllTrans x := ⟨mul_left_le x x⟩

@[simp] lemma mul_self_eq_of_allSet (x : L) [AllSet x] : x * x = x := by
  refine (mul_self_le x).antisymm (le_trans ?_ <| mul_right_le _ x)
  convert ← le_mul_mul x
  exact conv_eq x

lemma mul_eq_inf (x y : L) [AllSet x] [AllSet y] : x * y = x ⊓ y := by
  refine (le_inf (mul_right_le x y) (mul_left_le x y)).antisymm ?_
  nth_grw 1 [←mul_self_eq_of_allSet (x ⊓ y), inf_le_left, inf_le_right]

lemma mul_inf_assoc (x y z : L) [AllSet x] : x * y ⊓ z = x * (y ⊓ z) := by
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · grw [left_modular, mul_left_le xᵒ]
  · grw [inf_le_left]
  · grw [inf_le_right, mul_left_le]

lemma ext_le_allSet (x y : L) [AllSet x] [AllSet y] : x = y ↔ ∀ z [AllSet z], z ≤ x ↔ z ≤ y := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  apply eq_of_forall_le_iff
  intro w; constructor
  all_goals
    intro hw
    have : AllSet w := ⟨hw.trans <| le_one _⟩
    grind

section Domain

variable [OrderTop L]

def ldom (x : L) : L := x * ⊤ ⊓ 1

def rdom (x : L) : L := ⊤ * x ⊓ 1

instance (x : L) : AllSet (ldom x) where
  le_one := inf_le_right

instance (x : L) : AllSet (rdom x) where
  le_one := inf_le_right

@[simp, scoped grind =] lemma ldom_conv (x : L) : ldom xᵒ = rdom x := by
  convert conv_eq <| rdom x using 1
  rw [ldom, rdom, conv_inf, conv_mul, conv_eq ⊤, conv_eq 1]

@[simp, scoped grind =] lemma rdom_conv (x : L) : rdom xᵒ = ldom x := by
  convert conv_eq <| ldom x using 1
  rw [ldom, rdom, conv_inf, conv_mul, conv_eq ⊤, conv_eq 1]

@[gcongr, scoped grind .] lemma ldom_mono {x y : L} (h : x ≤ y) : ldom x ≤ ldom y :=
  inf_le_inf_right 1 (mul_left_mono h)

@[gcongr, scoped grind .] lemma rdom_mono {x y : L} (h : x ≤ y) : rdom x ≤ rdom y :=
  inf_le_inf_right 1 (mul_right_mono h)

@[simp, scoped grind =] lemma ldom_sup {L : Type*} [DistribAllegory L] [OrderTop L] (x y : L) :
    ldom (x ⊔ y) = ldom x ⊔ ldom y := by
  simp [ldom, inf_sup_right]

@[simp, scoped grind =] lemma rdom_sup {L : Type*} [DistribAllegory L] [OrderTop L] (x y : L) :
    rdom (x ⊔ y) = rdom x ⊔ rdom y := by
  simp [rdom, inf_sup_right]

@[simp] lemma ldom_of_allRefl (x : L) [AllRefl x] : ldom x = 1 := by
  refine inf_le_right.antisymm <| le_inf ?_ le_rfl
  simpa using mul_le_mul' (one_le' x) (one_le' ⊤)

@[simp] lemma rdom_of_allRefl (x : L) [AllRefl x] : rdom x = 1 := by
  refine inf_le_right.antisymm <| le_inf ?_ le_rfl
  simpa using mul_le_mul' (one_le' ⊤) (one_le' x)

lemma ldom_eq_rdom_of_allSymm (x : L) [AllSymm x] : ldom x = rdom x := by
  rw [←rdom_conv, conv_eq]

lemma ldom_mul_right_le (x y : L) : ldom (x * y) ≤ ldom x := by
  rw [ldom, ldom, mul_assoc]
  exact inf_le_inf_right 1 (mul_right_mono le_top)

lemma rdom_mul_left_le (x y : L) : rdom (x * y) ≤ rdom y := by
  rw [rdom, rdom, ←mul_assoc]
  exact inf_le_inf_right 1 (mul_left_mono le_top)

lemma ldom_mul_right_allRefl (x y : L) [AllRefl y] : ldom (x * y) = ldom x :=
  (ldom_mul_right_le x y).antisymm <| ldom_mono (mul_right_ge x y)

lemma rdom_mul_left_allRefl (x y : L) [AllRefl x] : rdom (x * y) = rdom y :=
  (rdom_mul_left_le x y).antisymm <| rdom_mono (mul_left_ge y x)

lemma ldom_le_self_mul_conv (x : L) : ldom x ≤ x * xᵒ := by
  convert! left_modular x ⊤ 1 using 1
  simp

lemma rdom_le_conv_mul_self (x : L) : rdom x ≤ xᵒ * x := by
  convert! right_modular ⊤ x 1 using 1
  simp

@[simp] lemma ldom_allSet (x : L) [AllSet x] : ldom x = x := by
  refine le_antisymm (ldom_le_self_mul_conv x |>.trans ?_) (le_inf (mul_right_ge x ⊤) (le_one x))
  simp

@[simp] lemma rdom_allSet (x : L) [AllSet x] : rdom x = x := by
  refine le_antisymm (rdom_le_conv_mul_self x |>.trans ?_) (le_inf (mul_left_ge x ⊤) (le_one x))
  simp

@[simp] lemma ldom_mul_self (x : L) : ldom x * x = x := by
  refine (mul_left_le (ldom x) x).antisymm ?_
  calc
    x = x ⊓ x * 1 := by simp
    _ ≤ x ⊓ x * ⊤ := by gcongr; exact le_top
    _ ≤ (1 ⊓ x * ⊤ * xᵒ) * x := by convert right_modular 1 x (x * ⊤) using 2; simp
    _ ≤ (1 ⊓ x * ⊤ * ⊤) * x := by gcongr; exact le_top
    _ = ldom x * x := by simp [ldom, inf_comm]

@[simp] lemma self_mul_rdom (x : L) : x * rdom x = x := by
  rw [←conv_conv (x * rdom x), conv_mul, conv_eq (rdom x), ←ldom_conv, ldom_mul_self, conv_conv]

lemma ldom_mul_top (x : L) : ldom x * ⊤ = x * ⊤ := by
  refine le_antisymm ?_ ?_
  · calc
      ldom x * ⊤ ≤ x * ⊤ * ⊤ ⊓ 1 * ⊤ := inf_mul_le ..
      _ = x * ⊤ ⊓ 1 * ⊤ := by simp
      _ ≤ x * ⊤ := inf_le_left ..
  · rw (occs := [1]) [←ldom_mul_self x, mul_assoc]
    exact mul_right_mono le_top

lemma top_mul_rdom (x : L) : ⊤ * rdom x = ⊤ * x := by
  rw [←conv_conv (⊤ * rdom x), conv_mul, conv_eq (rdom x), conv_top, ←ldom_conv, ldom_mul_top,
    conv_mul, conv_top, conv_conv]

lemma ldom_mul_ldom (x y : L) : ldom (x * ldom y) = ldom (x * y) := by
  rw [←ldom_mul_right_allRefl (x * ldom y) ⊤, mul_assoc, ldom_mul_top, ←mul_assoc,
    ldom_mul_right_allRefl _ ⊤]

lemma rdom_rdom_mul (x y : L) : rdom (rdom x * y) = rdom (x * y) := by
  rw [←rdom_mul_left_allRefl ⊤ (rdom x * y), ←mul_assoc, top_mul_rdom, mul_assoc,
    rdom_mul_left_allRefl ⊤ _]

theorem ldom_le_tfae_of_allSet (x y : L) [AllSet y] :
    [ldom x ≤ y, y * x = x, x ≤ y * x, x ≤ y * ⊤].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    rw [←ldom_mul_self x, ←mul_assoc, mul_eq_inf y (ldom x), inf_eq_right.mpr h]
  tfae_have 2 → 3 := Eq.ge
  tfae_have 3 → 4 | h => h.trans <| mul_right_mono le_top
  tfae_have 4 → 1 := by
    intro h
    rw [←ldom_allSet y, ←ldom_mul_right_allRefl y ⊤]
    exact ldom_mono h
  tfae_finish

lemma ldom_le_iff_mul_eq (x y : L) [AllSet y] : ldom x ≤ y ↔ y * x = x :=
  ldom_le_tfae_of_allSet x y |>.out 1 2

lemma ldom_le_iff_le_mul_top (x y : L) [AllSet y] : ldom x ≤ y ↔ x ≤ y * ⊤ :=
  ldom_le_tfae_of_allSet x y |>.out 1 4

lemma ldom_le_ldom_iff (x y : L) : ldom x ≤ ldom y ↔ x ≤ y * ⊤ := by
  rw [ldom_le_iff_le_mul_top x (ldom y), ldom_mul_top]

theorem rdom_le_tfae_of_allSet (x y : L) [AllSet y] :
    [rdom x ≤ y, x * y = x, x ≤ x * y, x ≤ ⊤ * y].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    rw [←self_mul_rdom x, mul_assoc, mul_eq_inf (rdom x) y, inf_eq_left.mpr h]
  tfae_have 2 → 3 := Eq.ge
  tfae_have 3 → 4 | h => h.trans <| mul_left_mono le_top
  tfae_have 4 → 1 := by
    intro h
    rw [←rdom_allSet y, ←rdom_mul_left_allRefl ⊤ y]
    exact rdom_mono h
  tfae_finish

lemma rdom_le_iff_mul_eq (x y : L) [AllSet y] : rdom x ≤ y ↔ x * y = x :=
  rdom_le_tfae_of_allSet x y |>.out 1 2

lemma rdom_le_iff_le_top_mul (x y : L) [AllSet y] : rdom x ≤ y ↔ x ≤ ⊤ * y :=
  rdom_le_tfae_of_allSet x y |>.out 1 4

lemma rdom_le_rdom_iff (x y : L) : rdom x ≤ rdom y ↔ x ≤ ⊤ * y := by
  rw [rdom_le_iff_le_top_mul x (rdom y), top_mul_rdom]

@[simp, scoped grind =>] lemma ldom_allSet_mul (x y : L) [AllSet x] :
    ldom (x * y) = x * ldom y := by rw [←ldom_mul_ldom, ldom_allSet]

@[simp, scoped grind =>] lemma rdom_mul_allSet (x y : L) [AllSet y] :
    rdom (x * y) = rdom x * y := by rw [←rdom_rdom_mul, rdom_allSet]

lemma eq_ldom_mul_of_eq_mul_allSet {x y z : L} [AllSet y] (h : x = y * z) :
    x = ldom x * z := by
  apply le_antisymm
  · nth_rw 1 [←ldom_mul_self x]
    exact mul_right_mono <| h ▸ mul_left_le y z
  · nth_rw 2 [h]
    gcongr
    rw [ldom_le_iff_le_mul_top, h]
    exact mul_right_mono le_top

lemma eq_mul_rdom_of_eq_mul_allSet {x y z : L} [AllSet z] (h : x = y * z) :
    x = y * rdom x := by
  rw [←conv_eq_conv_iff, conv_mul] at h ⊢
  convert eq_ldom_mul_of_eq_mul_allSet h using 2
  simp

lemma ldom_mul_allSet_le_allSet_iff (x y z : L) [AllSet y] [AllSet z] :
    ldom (x * y) ≤ z ↔ x * y ≤ z * x := by
  constructor <;> intro h
  · rw [ldom_le_iff_mul_eq] at h
    grw [←h, mul_right_le x y]
  · grw [ldom_le_iff_le_mul_top, h, le_top (a := x)]

lemma rdom_allSet_mul_le_allSet_iff (x y z : L) [AllSet x] [AllSet z] :
    rdom (x * y) ≤ z ↔ x * y ≤ y * z := by
  constructor <;> intro h
  · rw [rdom_le_iff_mul_eq] at h
    grw [←h, mul_assoc, mul_left_le x (y * z)]
  · grw [rdom_le_iff_le_top_mul, h, le_top (a := y)]

end Domain

section Conditions

variable {L : Type*} [DivisionAllegory L] [OrderTop L]

abbrev precond (x y : L) : L := (x \\ y * ⊤) ⊓ 1

scoped infix:65 " .\\\\. " => precond

lemma le_precond_iff (x y z : L) [AllSet x] [AllSet z] : x ≤ y .\\. z ↔ ldom (y * x) ≤ z := by
  simp_rw [le_inf_iff, le_one x, and_true, le_under_iff, ldom_le_iff_le_mul_top]

instance (x y : L) : AllSet (x .\\. y) := ⟨inf_le_right⟩

lemma ldom_mul_precond_le (x y : L) [AllSet y] : ldom (x * (x .\\. y)) ≤ y := by
  rw [←le_precond_iff]

lemma mul_precond_le_mul (x y : L) [AllSet y] : x * (x .\\. y) ≤ y * x :=
  ldom_mul_allSet_le_allSet_iff x (x .\\. y) y |>.mp (ldom_mul_precond_le x y)

lemma le_ldom_mul_precond (x y : L) [AllSet x] : x ≤ y .\\. ldom (y * x) := by
  rw [le_precond_iff]

lemma precond_eq_ldom (x y : L) [AllSet y] : x .\\. y = ldom (x \\ y * ⊤) := by
  rw [ext_le_allSet]
  intro z _
  nth_rw 2 [←ldom_allSet z]
  rw [le_precond_iff, ldom_le_iff_le_mul_top, ldom_le_ldom_iff, ←le_under_iff,
    under_top_mul_mul_top]

abbrev postcond (x y : L) : L := (⊤ * x // y) ⊓ 1

scoped infix:65 " .//. " => postcond

lemma le_postcond_iff (x y z : L) [AllSet x] [AllSet y] : x ≤ y .//. z ↔ rdom (x * z) ≤ y := by
  simp_rw [le_inf_iff, le_one x, and_true, le_over_iff, rdom_le_iff_le_top_mul]

instance (x y : L) : AllSet (x .//. y) := ⟨inf_le_right⟩

lemma rdom_postcond_mul_le (x y : L) [AllSet x] : rdom ((x .//. y) * y) ≤ x := by
  rw [←le_postcond_iff]

lemma postcond_mul_le_mul (x y : L) [AllSet x] : (x .//. y) * y ≤ y * x :=
  rdom_allSet_mul_le_allSet_iff (x .//. y) y x |>.mp (rdom_postcond_mul_le x y)

lemma le_rdom_postcond_mul (x y : L) [AllSet x] : x ≤ rdom (x * y) .//. y := by
  rw [le_postcond_iff]

lemma conv_precond_conv (x y : L) : xᵒ .\\. yᵒ = y .//. x := by
  rw [←conv_eq (xᵒ .\\. yᵒ), precond, ←conv_eq ⊤, ←conv_mul, ←conv_over, ←conv_eq 1, ←conv_inf,
    conv_conv]

lemma postcond_eq_rdom (x y : L) [AllSet x] : x .//. y = rdom (⊤ * x // y) := by
  rw [←conv_precond_conv, precond_eq_ldom, ←ldom_conv, conv_over, conv_mul, conv_top]

lemma conv_precond_allSymm (x y : L) [AllSymm y] : xᵒ .\\. y = y .//. x := by
  simp [←conv_precond_conv]

lemma conv_postcond_conv (x y : L) : xᵒ .//. yᵒ = y .\\. x := by
  simp [←conv_precond_conv]

lemma allSymm_postcond_conv (x y : L) [AllSymm x] : x .//. yᵒ = y .\\. x := by
  simp [←conv_postcond_conv]

@[simp] lemma mul_precond {L : Type*} [UnionDivAllegory L] (x y z : L) :
    (x .\\. z) * (y .\\. z) = (x ⊔ y) .\\. z := by
  simp [mul_eq_inf, precond]
  grind

@[simp] lemma mul_postcond {L : Type*} [UnionDivAllegory L] (x y z : L) :
    (x .//. y) * (x .//. z) = (x .//. y ⊔ z) := by
  simp [mul_eq_inf, postcond]
  grind

@[simp] lemma one_precond (x : L) [AllSet x] : 1 .\\. x = x := by
  rw [precond, under_one]
  exact ldom_allSet x

@[simp] lemma postcond_one (x : L) [AllSet x] : x .//. 1 = x := by
  rw [postcond, over_one]
  exact rdom_allSet x

lemma precond_le_precond_iff (w x y z : L) [AllSet x] [AllSet z] :
    w .\\. x ≤ y .\\. z ↔ w \\ x * ⊤ ≤ y \\ z * ⊤ := by
  rw [le_under_iff, ←ldom_le_iff_le_mul_top (y * (w \\ x * ⊤)), ←ldom_mul_ldom,
    ←le_precond_iff, ←precond_eq_ldom]

end Conditions

end Allegory
