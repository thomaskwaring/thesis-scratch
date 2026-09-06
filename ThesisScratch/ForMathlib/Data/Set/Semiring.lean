import Mathlib.Data.Set.Semiring
import Mathlib.Data.List.Induction

namespace SetSemiring

open Set List KStar Computability

variable {α : Type*}

instance : Membership α (SetSemiring α) where
  mem s x := x ∈ s.down

@[simp]
lemma mem_down_iff (x : α) (s : SetSemiring α) : x ∈ s.down ↔ x ∈ s := Iff.rfl

lemma le_iff_mem_of_mem (s t : SetSemiring α) : s ≤ t ↔ (∀ x ∈ s, x ∈ t) := Iff.rfl

lemma mem_of_mem_of_le {s t : SetSemiring α} (h : s ≤ t) {x : α} (hx : x ∈ s) : x ∈ t :=
  le_iff_mem_of_mem s t |>.mp h x hx

@[ext]
lemma ext {s t : SetSemiring α} (h : ∀ (x : α), x ∈ s ↔ x ∈ t) : s = t :=
  SetSemiring.down.injective <| by ext x; simpa using h x

lemma notMem_zero (x : α) : x ∉ (0 : SetSemiring α) := Set.notMem_empty x

lemma mem_add_iff (x : α) (s t : SetSemiring α) : x ∈ s + t ↔ x ∈ s ∨ x ∈ t :=
    Set.mem_union x s.down t.down

lemma mem_add_left {x : α} {s : SetSemiring α} (t : SetSemiring α) : x ∈ s → x ∈ s + t :=
  Set.mem_union_left t

lemma mem_add_right {x : α} {t : SetSemiring α} (s : SetSemiring α) : x ∈ t → x ∈ s + t :=
  Set.mem_union_right s

lemma mul_mem_mul [Mul α] {s t : SetSemiring α} {x y : α} (hx : x ∈ s) (hy : y ∈ t) :
    x * y ∈ s * t := Set.mul_mem_mul hx hy

lemma mem_mul_iff [Mul α] {s t : SetSemiring α} {x : α} :
    x ∈ s * t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := Set.mem_mul

@[simp]
lemma mem_one_iff [One α] (x : α) : x ∈ (1 : SetSemiring α) ↔ x = 1 := Set.mem_one

instance [Mul α] [One α] : KStar (SetSemiring α) where
  kstar s := Set.up {x | ∃ l : List α, (∀ y ∈ l, y ∈ s) ∧ x = l.prod}

lemma prod_mem_kstar [Mul α] [One α] {s : SetSemiring α} {l : List α} (h : ∀ x ∈ l, x ∈ s) :
    l.prod ∈ s∗ := ⟨l, h, rfl⟩

lemma mem_kstar_iff [Mul α] [One α] {s : SetSemiring α} {x : α} :
    x ∈ s∗ ↔ ∃ l : List α, (∀ y ∈ l, y ∈ s) ∧ x = l.prod := Iff.rfl

lemma one_mem_kstar [Mul α] [One α] (s : SetSemiring α) : 1 ∈ s∗ := by use []; simp

private protected lemma one_le_kstar [Mul α] [One α] (s : SetSemiring α) : 1 ≤ s∗ := by
  simpa [le_iff_mem_of_mem] using one_mem_kstar s

private protected lemma mul_kstar_le_kstar [Mul α] [One α] (s : SetSemiring α) : s * s∗ ≤ s∗ := by
  simp_rw [le_iff_mem_of_mem, mem_mul_iff, mem_kstar_iff]
  rintro _ ⟨x, hx, _, ⟨l, hl, rfl⟩, rfl⟩
  use x :: l
  simpa [hx]

private protected lemma kstar_mul_le_kstar [Monoid α] (s : SetSemiring α) : s∗ * s ≤ s∗ := by
  simp_rw [le_iff_mem_of_mem, mem_mul_iff, mem_kstar_iff]
  rintro _ ⟨_, ⟨l, hl, rfl⟩, x, hx, rfl⟩
  use l ++ [x]
  grind

private protected lemma mul_kstar_le_self [Monoid α] (s t : SetSemiring α) (h : t * s ≤ t) :
    t * s∗ ≤ t := by
  simp_rw [le_iff_mem_of_mem, mem_mul_iff, forall_exists_index, and_imp] at h ⊢
  simp_rw [mem_kstar_iff, existsAndEq, and_true, forall_exists_index, and_imp]
  rintro _ x hx l hl rfl
  induction l generalizing x with
  | nil => simpa
  | cons y l ih =>
    rw [prod_cons, ←mul_assoc]
    refine ih (x * y) ?_ (by grind)
    apply h (x * y) x hx
    use y
    grind

private protected lemma kstar_mul_le_self [Monoid α] (s t : SetSemiring α) (h : s * t ≤ t) :
    s∗ * t ≤ t := by
  simp_rw [le_iff_mem_of_mem, mem_mul_iff, forall_exists_index, and_imp] at h ⊢
  simp_rw [mem_kstar_iff, forall_exists_index, and_imp]
  rintro _ _ l hl rfl x hx rfl
  induction l using List.reverseRec generalizing x with
  | nil => simpa
  | append_singleton l y ih =>
    rw [prod_append, prod_cons, prod_nil, mul_one, mul_assoc]
    refine ih (by grind) (y * x) ?_
    refine h (y * x) y (by grind) ?_
    use x

noncomputable instance [Monoid α] : KleeneAlgebra (SetSemiring α) where
  one_le_kstar := SetSemiring.one_le_kstar
  mul_kstar_le_kstar := SetSemiring.mul_kstar_le_kstar
  kstar_mul_le_kstar := SetSemiring.kstar_mul_le_kstar
  mul_kstar_le_self := SetSemiring.mul_kstar_le_self
  kstar_mul_le_self := SetSemiring.kstar_mul_le_self

end SetSemiring
