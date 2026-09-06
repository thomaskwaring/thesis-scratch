import ThesisScratch.ForMathlib.RelationAlgebra.Set

namespace Allegory

open UnionAllegory DivisionAllegory OrderHom

def AllWF {L : Type*} [Allegory L] [OrderBot L] (x : L) : Prop := ∀ y : L, y ≤ y * x → y ≤ ⊥

lemma AllWF.apply {L : Type*} [Allegory L] [OrderBot L] {x y : L} (hx : AllWF x) (hy : y ≤ y * x) :
    y ≤ ⊥ := hx y hy

theorem allWF_tfae {L : Type*} [UnionAllegory L] [OrderTop L] (x : L) :
    [AllWF x, ∀ y [AllSet y], y ≤ rdom (y * x) → y ≤ ⊥,
    ∀ y, ⊤ * y = y → y ≤ y * x → y ≤ ⊥].TFAE := by
  tfae_have 1 → 3 := fun h y _ hy => h.apply hy
  tfae_have 3 → 1 := by
    intro h y hy
    exact (mul_left_ge y ⊤).trans <| h (⊤ * y) (mul_left_idem ⊤ y) (by nth_grw 1 [mul_assoc, hy])
  tfae_have 2 → 3 := by
    intro h y hy hy'
    specialize h (rdom y) (by nth_grw 1 [rdom_rdom_mul y x, hy'])
    grw [←self_mul_rdom y, h, mul_bot]
  tfae_have 3 → 2 := by
    intro h y _ hy
    refine (mul_left_ge y ⊤).trans <| h (⊤ * y) (mul_left_idem ⊤ y) ?_
    nth_grw 1 [hy, top_mul_rdom, ←mul_assoc]
  tfae_finish

def AllInd {L : Type*} [DivisionAllegory L] [OrderTop L] (x : L) : Prop :=
    ∀ y : L, x \\ y ≤ y → ⊤ ≤ y

lemma AllInd.apply {L : Type*} [DivisionAllegory L] [OrderTop L] {x y : L} (hx : AllInd x)
    (hy : x \\ y ≤ y) : ⊤ ≤ y := hx y hy

theorem allInd_tfae {L : Type*} [UnionDivAllegory L] (x : L) :
    [AllInd x, ∀ y [AllSet y], x .\\. y ≤ y → 1 ≤ y,
    ∀ y, y * ⊤ = y → x \\ y ≤ y → ⊤ ≤ y].TFAE := by
  tfae_have 1 → 3 := fun h y _ hy => h.apply hy
  tfae_have 3 → 1 := by
    intro h y hy
    refine (h (y // ⊤) ?_ ?_).trans ?_
    · refine le_antisymm ?_ (mul_right_ge ..)
      grw [le_over_iff, mul_right_idem (y // ⊤) ⊤, over_mul_le]
    · grw [over_under_assoc, hy]
    · grw [mul_right_ge (y // ⊤) ⊤, over_mul_le]
  tfae_have 2 → 3 := by
    intro h y hy hy'
    rw [←one_mul ⊤, ←hy, ←ldom_mul_top y]
    refine mul_left_mono (h (ldom y) ?_)
    grw [precond, ldom_mul_top, hy, hy', ldom, hy]
  tfae_have 3 → 2 := by
    intro h y _ hy
    rw [←ldom_allSet 1, ldom_le_iff_le_mul_top]
    refine le_top.trans <| h (y * ⊤) (mul_right_idem y ⊤) <| ?_
    rwa [←ldom_le_iff_le_mul_top, ←precond_eq_ldom]
  tfae_finish

lemma AllInd.apply_allSet {L : Type*} [UnionDivAllegory L] {x y : L} (hx : AllInd x) [AllSet y]
    (h : x .\\. y ≤ y) : 1 ≤ y := by
  have := allInd_tfae x |>.out 1 2 |>.mp hx
  exact this y h

theorem AllInd.allWF {L : Type*} [UnionDivAllegory L] {x : L} (hx : AllInd x) : AllWF x := by
  intro y hy
  grw [mul_right_ge y ⊤, ←le_under_iff]
  apply hx
  nth_grw 1 [le_under_iff, hy, mul_assoc, mul_under_le, mul_under_le]

theorem AllWF.allInd {L : Type*} [BooleanAllegory L] {x : L} (hx : AllWF x) : AllInd x := by
  intro y hy
  rw [←compl_le_compl_iff_le, compl_top, ←conv_le_conv_iff, conv_compl, conv_bot]
  apply hx
  rwa [←conv_le_conv_iff, conv_mul, conv_compl, compl_le_iff_compl_le, conv_conv, ←under_eq]

theorem allInd_iff_allWF {L : Type*} [BooleanAllegory L] (x : L) : AllInd x ↔ AllWF x :=
  ⟨AllInd.allWF, AllWF.allInd⟩

lemma AllWF.anti {L : Type*} [Allegory L] [OrderBot L] {x y : L} (h : x ≤ y) (hy : AllWF y) :
    AllWF x := fun z hz => hy z <| by grw [←h, ←hz]

lemma AllInd.anti {L : Type*} [DivisionAllegory L] [OrderTop L] {x y : L} (h : x ≤ y)
    (hy : AllInd y) : AllInd x := fun z hz => hy z <| by grw [←h, hz]

lemma AllWF.transGen {L : Type*} [CompleteAllegory L] {x : L} (hx : AllWF x) : AllWF x⁺ := by
  intro y h
  grw [h, le_sup_right (a := y * 1) (b := y * x⁺)]
  apply hx
  nth_grw 1 [←mul_sup, sup_mul, mul_assoc, mul_assoc, ←mul_sup, one_mul, transGen_eq_sup', h,
    mul_sup, mul_one, mul_assoc, mul_self_le, sup_idem]

@[simp] theorem allWF_transGen_iff {L : Type*} [CompleteAllegory L] (x : L) :
    AllWF x⁺ ↔ AllWF x := ⟨fun h => h.anti (le_transGen x), AllWF.transGen⟩

lemma AllInd.transGen {L : Type*} [CompleteAllegory L] {x : L} (hx : AllInd x) : AllInd x⁺ := by
  intro y h
  grw [←h, ←transGen_eq_sup, sup_under]
  refine hx _ (le_inf ?_ ?_)
  · grw [under_inf, le_under_iff, mul_inf_le, mul_under_le, mul_under_le, ←sup_under,
      transGen_eq_sup, h]
  · rw [under_inf, under_under x x y, under_under, ←sup_under, mul_assoc, ←mul_sup,
      transGen_eq_sup']

@[simp] theorem allInd_transGen_iff {L : Type*} [CompleteAllegory L] (x : L) :
    AllInd x⁺ ↔ AllInd x := ⟨fun h => h.anti (le_transGen x), AllInd.transGen⟩

theorem newmann {L : Type*} [CompleteAllegory L] {x y : L} (hwf : AllInd (x ⊔ yᵒ))
    (hcon : x * y ≤ y⋆ * x⋆) : WeaklyCommute x⋆ y⋆ := by
  set a := ((x⋆ \\ (y⋆ * x⋆)) // y⋆) ⊓ 1 with heq
  -- `a` is the set on which the conclusion holds...
  have ha (b : L) [AllSet b] : b ≤ a ↔ x⋆ * b * y⋆ ≤ y⋆ * x⋆ := by
    simp [heq, le_inf_iff, le_over_iff, le_under_iff, ←mul_assoc, le_one b]
  -- so we show by induction that `a` is the whole domain.
  suffices 1 ≤ a by
    nth_rw 1 [WeaklyCommute, ←le_under_iff, ←one_mul y⋆, ←le_over_iff]
    exact this.trans inf_le_left
  -- this lemma amounts to the case split on the reflexive-transitive closure
  have h_rtg (b c d : L) : b⋆ * c * d⋆ = c ⊔ b⋆ * b * c ⊔ c * d * d⋆ ⊔ b⋆ * b * c * d * d⋆ := by
    nth_rw 1 [←reflTransGen_eq_sup' b, ←reflTransGen_eq_sup d]
    simp [←mul_assoc, ←sup_assoc]
  apply hwf.apply_allSet
  simp_rw [←mul_precond, ha, h_rtg, sup_le_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  -- cases where one reduction is reflexive are easy
  · grw [le_one ((x .\\. a) * (yᵒ .\\. a)), one_le' (y⋆ * x⋆)]
  · grw [le_one ((x .\\. a) * (yᵒ .\\. a)), mul_one, reflTransGen_mul_le_reflTransGen, ←mul_left_ge]
  · grw [le_one ((x .\\. a) * (yᵒ .\\. a)), one_mul, mul_reflTransGen_le_reflTransGen,
      ←mul_right_ge]
  -- the key step: use local confluence (`hcon`), the inductive hypothesis (as `ha`) and
  -- transitivity (`mul_self_le`).
  · calc
    _ = x⋆ * (x * (x .\\. a)) * ((yᵒ .\\. a) * y * y⋆) := by simp only [←mul_assoc]
    _ ≤ x⋆ * a * (x * y) * a * y⋆ := by
        grw [mul_precond_le_mul, conv_precond_allSymm, postcond_mul_le_mul]; simp [←mul_assoc]
    _ ≤ y⋆ * (x⋆ * x⋆) * a * y⋆ := by grw [hcon, ←mul_assoc, (ha a).mp le_rfl]; simp
    _ ≤ y⋆ * (x⋆ * a * y⋆) := by grw [mul_self_le]; simp [←mul_assoc]
    _ ≤ y⋆ * x⋆ := by grw [(ha a).mp le_rfl, ←mul_assoc, mul_self_le]



end Allegory
