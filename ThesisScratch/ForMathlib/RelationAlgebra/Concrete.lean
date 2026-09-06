import ThesisScratch.ForMathlib.RelationAlgebra.WellFounded
import ThesisScratch.ForMathlib.Basic.Relation

variable {α : Type*}

open Relation Function Set

@[implicit_reducible]
def compMonoid (α : Type*) : Monoid (α → α → Prop) where
  mul := Comp
  mul_assoc _ _ _ := Relation.comp_assoc ..
  one := (· = ·)
  one_mul _ := eq_comp
  mul_one _ := comp_eq

namespace Allegory

scoped instance (α : Type*) : RelationAlgebra (α → α → Prop) where
  __ := compMonoid α
  elim := by
    intro s r r' h x y ⟨z, hxz, hzy⟩
    use z, hxz, h _ _ hzy
  conv := swap
  conv_le_iff_le_conv s r := by
    constructor <;> intro h x y hxy <;> exact h y x hxy
  conv_mul _ _ := flip_comp
  left_modular s r t x y := by
    intro ⟨⟨z, hxz, hzy⟩, ht⟩
    use z, hxz, hzy, x
  over s r x y := ∀ z, r y z → s x z
  le_over_iff s r t := by
    constructor
    · intro h x y ⟨z, hxz, hzy⟩
      exact h x z hxz y hzy
    · intro h x y hxy z hyz
      exact h x z ⟨y, hxy, hyz⟩

lemma conv_iff (r : α → α → Prop) (x y : α) : rᵒ x y ↔ r y x := Iff.rfl

lemma rel_top_eq : (⊤ : α → α → Prop) = fun _ _ => True := rfl

lemma rel_bot_eq : (⊥ : α → α → Prop) = fun _ _ => False := rfl

lemma over_iff (s r : α → α → Prop) (x y : α) : (s // r) x y ↔ ∀ z, r y z → s x z := Iff.rfl

lemma under_iff (s r : α → α → Prop) (x y : α) : (s \\ r) x y ↔ ∀ z, s z x → r z y := Iff.rfl

lemma allRefl_iff_refl (r : α → α → Prop) : AllRefl r ↔ Std.Refl r :=
  ⟨fun ⟨h⟩ => ⟨fun x => h x x rfl⟩, fun ⟨h⟩ => ⟨fun x _ hxy => hxy ▸ (h x)⟩⟩

lemma allSymm_iff_allSymm (r : α → α → Prop) : AllSymm r ↔ Std.Symm r :=
  ⟨fun ⟨h⟩ => ⟨fun _ _ hxy => h ▸ hxy⟩, fun ⟨h⟩ => allSymm_of_le_conv h⟩

lemma allTrans_iff_isTrans (r : α → α → Prop) : AllTrans r ↔ IsTrans α r :=
  ⟨fun ⟨h⟩ => ⟨fun x y z hxy hyz => h x z ⟨y, hxy, hyz⟩⟩,
    fun ⟨h⟩ => ⟨fun x z ⟨y, hxy, hyz⟩ => h x y z hxy hyz⟩⟩

lemma rel_reflGen (r : α → α → Prop) : r⁼ = ReflGen r := by
  ext x y
  constructor
  · rintro (h | rfl)
    · exact .single h
    · exact .refl
  · rintro (_ | h)
    · exact Or.inr rfl
    · exact Or.inl h

lemma rel_symmGen (r : α → α → Prop) : rˢ = SymmGen r := by
  ext x y
  simp [SymmGen, conv]

lemma rel_transGen (r : α → α → Prop) : r⁺ = TransGen r := by
  apply le_antisymm
  · have : AllTrans (TransGen r) := by rw [allTrans_iff_isTrans]; infer_instance
    rw [transGen_le]
    exact TransGen.self_le
  · intro x y h
    induction h with
    | single h => exact le_transGen r _ _ h
    | tail h h' ih => exact transGen_mul_le_transGen r _ _ ⟨_, ih, h'⟩

def OfSet (s : Set α) : α → α → Prop := fun x y => x = y ∧ x ∈ s

instance allSet_setOf (s : Set α) : AllSet (OfSet s) := ⟨fun _ _ => And.left⟩

lemma ldom_eq_ofSet_dom (r : α → α → Prop) : ldom r = OfSet (dom r) := by
  ext x y
  constructor
  · intro ⟨⟨z, h, _⟩, heq⟩
    exact ⟨heq, ⟨z, h⟩⟩
  · intro ⟨heq, z, h⟩
    exact ⟨⟨z, h, trivial⟩, heq⟩

lemma rdom_eq_ofSet_cod (r : α → α → Prop) : rdom r = OfSet (cod r) := by
  ext x y
  constructor
  · intro ⟨⟨z, _, h⟩, heq⟩
    exact ⟨heq, ⟨z, heq ▸ h⟩⟩
  · intro ⟨heq, ⟨z, h⟩⟩
    exact ⟨⟨z, trivial, heq ▸ h⟩, heq⟩

@[simp] lemma dom_ofSet (a : Set α) : dom (OfSet a) = a := by
  ext x
  simp [dom, OfSet]

lemma ofSet_dom (r : α → α → Prop) [AllSet r] : OfSet (dom r) = r := by
  nth_rw 2 [←ldom_allSet r]
  exact (ldom_eq_ofSet_dom r).symm

lemma bijOn_ofSet : BijOn (α := Set α) OfSet univ {r | AllSet r} := by
  refine ⟨fun a _ => allSet_setOf a, ?_, ?_⟩
  · intro a _ b _ heq
    convert congr_arg dom heq <;> simp
  · intro r (_ : AllSet r)
    use dom r, trivial, ofSet_dom r

lemma precond_ofSet_eq_ofSet (r : α → α → Prop) (a : Set α) :
    r .\\. (OfSet a) = OfSet {x | ∀ y, r y x → y ∈ a} := by
  rw [precond_eq_ldom, ldom_eq_ofSet_dom]
  congr
  ext x
  constructor
  · intro ⟨y, h⟩ z hzx
    obtain ⟨_, ⟨_, ha⟩, _⟩ := h z hzx
    exact ha
  · intro hx
    use x
    intro y hyx
    use! y, hx y hyx, trivial

lemma postcond_ofSet_eq_ofSet (r : α → α → Prop) (a : Set α) :
    (OfSet a) .//. r = OfSet {x | ∀ y, r x y → y ∈ a} := by
  rw [←conv_precond_allSymm, precond_ofSet_eq_ofSet]
  rfl

theorem allInd_iff_wellFounded (r : α → α → Prop) : AllInd r ↔ WellFounded r := by
  refine ⟨fun h => ⟨?_⟩, fun h => ?_⟩
  · suffices ⊤ ≤ fun x _ => Acc r x from fun a => this a a trivial
    apply h
    intro x y h
    exact ⟨x, h⟩
  · intro s hs x y _
    induction x using h.induction with
    | h x hx =>
      apply hs
      intro z hz
      exact hx z hz trivial

end Allegory
