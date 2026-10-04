import ThesisScratch.ForMathlib.RelationAlgebra.WellFounded
import ThesisScratch.ForMathlib.Basic.Relation
import Mathlib.Data.Rel
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Sublattice

variable {α : Type*}

open Relation Function Set

namespace Allegory

/-- Binary endorelations as a relation algebra. -/
scoped instance (α : Type*) : RelationAlgebra (α → α → Prop) where
  mul := Comp
  mul_assoc _ _ _ := Relation.comp_assoc ..
  one := (· = ·)
  one_mul _ := eq_comp
  mul_one _ := comp_eq
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

/-- Interpret a set as a coreflexive relation. -/
def OfSet (s : Set α) : α → α → Prop := fun x y => x = y ∧ x ∈ s

instance allSet_setOf (s : Set α) : AllSet (OfSet s) := ⟨fun _ _ => And.left⟩

lemma ldom_eq_ofSet_dom (r : α → α → Prop) : ldom r = OfSet (dom r) := by
  ext x y
  constructor
  · intro ⟨⟨z, h, _⟩, heq⟩
    exact ⟨heq, ⟨z, h⟩⟩
  · intro ⟨heq, z, h⟩
    exact ⟨⟨z, h, heq ▸ h⟩, heq⟩

lemma rdom_eq_ofSet_cod (r : α → α → Prop) : rdom r = OfSet (cod r) := by
  ext x y
  constructor
  · intro ⟨⟨z, _, h⟩, heq⟩
    exact ⟨heq, ⟨z, heq ▸ h⟩⟩
  · intro ⟨heq, ⟨z, h⟩⟩
    exact ⟨⟨z, h, heq ▸ h⟩, heq⟩

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

open SetRel in
instance : RelationAlgebra (SetRel α α) where
  mul := comp
  mul_assoc := comp_assoc
  one := SetRel.id
  one_mul := id_comp
  mul_one := comp_id
  elim _ _ _ := comp_subset_comp_right
  conv := inv
  conv_le_iff_le_conv a b := by grind [inv]
  conv_mul := inv_comp
  left_modular x y z := by
    intro (a, c) ⟨⟨b, hab, hbc⟩, hac⟩
    use! b, hab, hbc, a, hab, hac
  over x y := {(a, b) | ∀ c, b ~[y] c → a ~[x] c}
  le_over_iff x y z := by
    constructor
    · intro h (a, b) ⟨c, hac, hcb⟩
      exact h hac b hcb
    · intro h (a, b) hab c hbc
      exact h ⟨b, hab, hbc⟩

open Pointwise in
instance {G : Type*} [Group G] : CompleteAllegory' (Set G) where
  __ := Set.monoid
  __ := Set.instMulLeftMono
  conv s := s⁻¹
  conv_le_iff_le_conv _ _ := Set.inv_subset
  conv_mul := DivisionMonoid.mul_inv_rev
  left_modular s t u := by
    rintro _ ⟨⟨x, hx, y, hy, rfl⟩, hu⟩
    use! x, hx, y, hy, x⁻¹, inv_mem_inv.mpr hx, x * y, hu
    simp
  sSup_mul' := Set.image2_sUnion_left (· * ·)

instance {G : Type*} [Group G] : RelationAlgebra (Set G) where

-- From Chris Henson's formalisation

structure ProperRelationAlgebra (X : Type*) extends Sublattice (SetRel X X) where
  /-- The largest relation, used as the Boolean top. -/
  top : SetRel X X
  /-- The top belongs to the algebra and contains every relation in it. -/
  isGreatest_top : IsGreatest carrier top
  /-- Closure under complement relative to the top. -/
  compl_mem' {R} : R ∈ carrier → top \ R ∈ carrier
  /-- The identity relation belongs to the algebra. -/
  id_mem' : SetRel.id ∈ carrier
  /-- Closure under relational composition. -/
  comp_mem' {R S} : R ∈ carrier → S ∈ carrier → R.comp S ∈ carrier
  /-- Closure under converse. -/
  inv_mem' {R} : R ∈ carrier → R.inv ∈ carrier

namespace ProperRelationAlgebra

variable {X : Type*} {P : ProperRelationAlgebra X}

@[ext]
protected theorem ext {P Q : ProperRelationAlgebra X} (h : P.carrier = Q.carrier) : P = Q := by
  have : P.top = Q.top := P.isGreatest_top.unique (h ▸ Q.isGreatest_top)
  rcases P with ⟨⟨_⟩, _⟩; rcases Q with ⟨⟨_⟩, _⟩
  congr

/-- The type of relations belonging to a proper relation algebra. -/
abbrev Carrier (P : ProperRelationAlgebra X) : Type _ := P.carrier

instance (P : ProperRelationAlgebra X) : BooleanAlgebra P.Carrier where
  toDistribLattice := inferInstanceAs (DistribLattice P.toSublattice)
  top := ⟨P.top, P.isGreatest_top.1⟩
  bot := ⟨∅, Set.sdiff_self ▸ P.compl_mem' P.isGreatest_top.1⟩
  compl R := ⟨P.top \ R.val, P.compl_mem' R.prop⟩
  le_top R := P.isGreatest_top.2 R.prop
  bot_le _ := Set.empty_subset _
  inf_compl_le_bot R := fun _ ⟨hR, _, hn⟩ ↦ hn hR
  top_le_sup_compl R := show P.top ⊆ R.val ∪ (P.top \ R.val) from le_sup_sdiff

instance (P : ProperRelationAlgebra X) : Monoid P.Carrier where
  one := ⟨SetRel.id, P.id_mem'⟩
  mul R S := ⟨R.val.comp S.val, P.comp_mem' R.prop S.prop⟩
  one_mul R := Subtype.ext (SetRel.id_comp R.val)
  mul_one R := Subtype.ext (SetRel.comp_id R.val)
  mul_assoc R S T := Subtype.ext (SetRel.comp_assoc R.val S.val T.val)

lemma coe_le_coe {r s : P.Carrier} : (↑r : SetRel X X) ≤ s ↔ r ≤ s := Iff.rfl

lemma coe_mul {r s : P.Carrier} : r * s = (r : SetRel X X) * s := rfl

instance booleanAllegory' (P : ProperRelationAlgebra X) : BooleanAllegory' P.Carrier where
  elim _ _ _ h := coe_le_coe.mp <| mul_right_mono h
  conv r := ⟨r.val.inv, P.inv_mem' r.prop⟩
  conv_le_iff_le_conv := by grind [=_ coe_le_coe, SetRel.inv]
  conv_mul _ _ := Subtype.ext <| SetRel.inv_comp ..
  left_modular
    | ⟨r, _⟩, ⟨s, _⟩, ⟨t, _⟩, ⟨x, y⟩, ⟨⟨z, hr, hs⟩, ht⟩ => ⟨z, hr, hs, x, hr, ht⟩
  mul_sup := by
    intro ⟨r, _⟩ ⟨s, _⟩ ⟨t, _⟩
    apply Subtype.ext
    convert SetRel.comp_sUnion r {s, t}
    all_goals simp; rfl
  mul_bot r := Subtype.ext <| SetRel.comp_empty r.val

instance (P : ProperRelationAlgebra X) : BooleanAllegory P.Carrier := BooleanAllegory.mk' P.Carrier

end ProperRelationAlgebra

end Allegory
