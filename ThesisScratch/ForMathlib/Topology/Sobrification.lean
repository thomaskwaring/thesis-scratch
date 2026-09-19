import Mathlib.Topology.Order.Category.FrameAdjunction
import Mathlib.Topology.Sober
import Mathlib.Order.Irreducible

open CategoryTheory Order Set TopologicalSpace Topology

lemma OrderIso.supIrred_apply {α β : Type*} [SemilatticeSup α] [SemilatticeSup β] (e : α ≃o β)
    {a : α} (ha : SupIrred a) : SupIrred (e a) := by
  constructor
  · rw [e.isMin_apply]
    exact ha.not_isMin
  · intro b c h
    rw [← e.symm_apply_eq, e.symm.map_sup] at h
    obtain (rfl | rfl) := ha.2 h <;> simp

lemma OrderIso.infIrred_apply {α β : Type*} [SemilatticeInf α] [SemilatticeInf β] (e : α ≃o β)
    {a : α} (ha : InfIrred a) : InfIrred (e a) := by
  constructor
  · rw [e.isMax_apply]
    exact ha.1
  · intro b c h
    rw [← e.symm_apply_eq, e.symm.map_inf] at h
    obtain (rfl | rfl) := ha.2 h <;> simp

lemma OrderIso.supIrred_apply_iff {α β : Type*} [SemilatticeSup α] [SemilatticeSup β] (e : α ≃o β)
    (a : α) : SupIrred (e a) ↔ SupIrred a := by
  refine ⟨?_, e.supIrred_apply⟩
  simpa using e.symm.supIrred_apply (a := e a)

lemma OrderIso.infIrred_apply_iff {α β : Type*} [SemilatticeInf α] [SemilatticeInf β] (e : α ≃o β)
    (a : α) : InfIrred (e a) ↔ InfIrred a := by
  refine ⟨?_, e.infIrred_apply⟩
  simpa using e.symm.infIrred_apply (a := e a)

lemma Closeds.coe_complOrderIso_apply {X : Type*} [TopologicalSpace X] (s : Closeds X) :
    OrderDual.ofDual (Closeds.complOrderIso X s) = (s : Set X)ᶜ := rfl

lemma isIrreducible_coe_iff_supIrred {X : Type*} [TopologicalSpace X] (s : Closeds X) :
    IsIrreducible (s : Set X) ↔ SupIrred s := by
  simp only [IsIrreducible, nonempty_iff_ne_empty, ne_eq,
    isPreirreducible_iff_isClosed_union_isClosed, ← supPrime_iff_supIrred, SupPrime,
    isMin_iff_eq_bot, ← Closeds.coe_eq_empty, and_congr_right_iff]
  intro _
  constructor
  · intro h ⟨t, ht⟩ ⟨t', ht'⟩ h'
    exact h t t' ht ht' h'
  · intro h t t' ht ht' h'
    exact @h ⟨t, ht⟩ ⟨t', ht'⟩ h'

lemma isIrreducible_compl_coe_iff_infIrred {X : Type*} [TopologicalSpace X] (u : Opens X) :
    IsIrreducible (u : Set X)ᶜ ↔ InfIrred u := by
  rw [← supIrred_toDual, ← (Closeds.complOrderIso X).symm.supIrred_apply_iff,
    ← isIrreducible_coe_iff_supIrred]
  rfl

lemma compl_inter_nonempty_iff {α : Type*} {s t : Set α} : (sᶜ ∩ t).Nonempty ↔ ¬ t ⊆ s := by
  rw [inter_comm, Set.inter_compl_nonempty_iff]

lemma isPreirreducible_compl_iff {X : Type*} [TopologicalSpace X] (s : Set X) :
    IsPreirreducible sᶜ ↔ ∀ u v, IsOpen u → IsOpen v → u ∩ v ⊆ s → (u ⊆ s ∨ v ⊆ s) := by
  simp_rw [IsPreirreducible, compl_inter_nonempty_iff]
  grind

namespace Locale.PT

variable {L : Type*} [CompleteLattice L]

lemma isClosed_iff (S : Set (PT L)) : IsClosed S ↔ ∃ u, {x | ¬ x u} = S := by
  simp only [← isOpen_compl_iff, isOpen_iff, Set.ext_iff]
  congr! 3
  grind

lemma specializes_iff (x y : PT L) : x ⤳ y ↔ y ≤ x := by
  simp [specializes_iff_forall_open, isOpen_iff, LE.le]

lemma closure_singleton_eq (x : PT L) : closure {x} = Set.Iic x := by
  grind [specializes_iff_mem_closure, =_ specializes_iff]

instance : T0Space (PT L) where
  t0 := by simp +contextual [inseparable_iff_specializes_and, specializes_iff, le_antisymm_iff]

instance : QuasiSober (PT L) where
  sober := by
    intro S ⟨h_ne, h_irred⟩ h_closed
    let x : L → Prop := fun u ↦ ∃ y ∈ S, y u
    have hinf (u v : L) : x (u ⊓ v) = x u ⊓ x v := by
      simp_rw [x, map_inf, inf_Prop_eq, eq_iff_iff]
      refine ⟨fun h ↦ ⟨h.imp ?_, h.imp ?_⟩, fun ⟨⟨y, hy, hyu⟩, z, hz, hzv⟩ ↦ ?irred⟩
      case irred => exact h_irred {x | x u} {x | x v} ⟨u, rfl⟩ ⟨v, rfl⟩ ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩
      all_goals simp +contextual
    have htop : x ⊤ = ⊤ := by simpa [x]
    have hsup (s : Set L) : x (sSup s) = sSup (x '' s) := by
      simp_rw [x, map_sSup, sSup_image, iSup_Prop_eq, eq_iff_iff, ← exists_prop]
      exact exists₂_comm
    use {toFun := x, map_inf' := hinf, map_top' := htop, map_sSup' := hsup}
    obtain ⟨u, rfl⟩ := isClosed_iff S |>.mp h_closed
    simp [isGenericPoint_def, Set.ext_iff, ← specializes_iff_mem_closure, specializes_iff, x,
      LE.le]
    grind

def homToOpens (L : Type*) [CompleteLattice L] : FrameHom L (Opens <| PT L) where
  toFun u := ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

lemma homToOpens_surjective : (homToOpens L : L → _).Surjective := by
  intro ⟨_, u, rfl⟩
  use (discharger := rfl) u

lemma isInducing_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] :
    IsInducing (localePointOfSpacePoint X) where
  eq_induced := by
    ext u
    simp_rw [isOpen_induced_iff, isOpen_iff, exists_exists_eq_and, preimage_ofPred_eq,
      localePointOfSpacePoint_toFun, SetLike.setOfPred_mem_eq]
    exact ⟨fun hu ↦ ⟨⟨u, hu⟩, rfl⟩, fun ⟨⟨u', hu'⟩, heq⟩ ↦ heq ▸ hu'⟩

def opensEquivOpensPtOpens (X : Type*) [TopologicalSpace X] : Opens X ≃ Opens (PT (Opens X)) where
  toFun := homToOpens (Opens X)
  invFun :=
    Opens.comap ⟨localePointOfSpacePoint X, (isInducing_localePointOfSpacePoint X).continuous⟩
  right_inv := by rintro ⟨v, u, rfl⟩; ext; rfl

lemma localePointOfSpacePoint_injective_iff_t0Space (X : Type*) [TopologicalSpace X] :
    (localePointOfSpacePoint X).Injective ↔ T0Space X :=
  ⟨(t0Space_of_injective_of_continuous · (isInducing_localePointOfSpacePoint X).continuous),
    fun _ ↦ (isInducing_localePointOfSpacePoint X).injective⟩

lemma isEmbedding_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (localePointOfSpacePoint X) where
  eq_induced := (isInducing_localePointOfSpacePoint X).eq_induced
  injective := (isInducing_localePointOfSpacePoint X).injective

protected def toCloseds {X : Type*} [TopologicalSpace X] (f : PT <| Opens X) : Closeds X :=
  (sSup {v : Opens X | ¬ f v}).compl

private lemma map_toCloseds_apply_compl {X : Type*} [TopologicalSpace X] (f : PT (Opens X)) :
    f (sSup {v | ¬ f v}) = ⊥ := by simp; grind

private lemma subset_toCloseds_apply_compl_iff {X : Type*} [TopologicalSpace X] {f : PT (Opens X)}
    {u : Set X} (hu : IsOpen u) : u ⊆ ↑(sSup {v : Opens X | ¬ f v}) ↔ ¬ f ⟨u, hu⟩ := by
  constructor
  · intro (h : ⟨u, hu⟩ ≤ sSup {v | ¬ f v})
    convert OrderHomClass.monotone f h
    rw [map_toCloseds_apply_compl, Prop.bot_eq_false]
  · exact le_sSup (s := {v | ¬ f v})

lemma isIrreducible_toCloseds {X : Type*} [TopologicalSpace X] (f : PT <| Opens X) :
    IsIrreducible (f.toCloseds : Set X) := by
  constructor
  · rw [PT.toCloseds, Opens.coe_compl, nonempty_compl, Ne, Opens.coe_eq_univ]
    refine fun h ↦ bot_ne_top (α := Prop) ?_
    rw [← map_top f, ← map_toCloseds_apply_compl f, h]
  · rw [PT.toCloseds, Opens.coe_compl, isPreirreducible_compl_iff]
    intro u v hu hv
    suffices f ⟨u ∩ v, hu.inter hv⟩ ↔ f ⟨u, hu⟩ ∧ f ⟨v, hv⟩ by
      grind [subset_toCloseds_apply_compl_iff]
    convert! ← map_inf (α := Opens X) (β := Prop) f (⟨u, hu⟩ : Opens X) ⟨v, hv⟩
    ext; exact eq_iff_iff

@[simps]
def _root_.IsIrreducible.toPTOpens {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsIrreducible s) : PT (Opens X) where
  toFun u := (s ∩ u).Nonempty
  map_inf' u v := by
    simp_rw [Opens.coe_inf, inf_Prop_eq, eq_iff_iff]
    exact ⟨fun ⟨x, hx, hu, hv⟩ ↦ ⟨⟨x, hx, hu⟩, ⟨x, hx, hv⟩⟩,
      fun ⟨hu, hv⟩ ↦ h.2 u v u.isOpen v.isOpen hu hv⟩
  map_top' := by simpa using h.nonempty
  map_sSup' T := by simp [sSup_image, Set.inter_iUnion]

@[simp] lemma toPTOpens_toCloseds {X : Type*} [TopologicalSpace X] (f : PT (Opens X)) :
    f.isIrreducible_toCloseds.toPTOpens = f := by
  ext u
  simp only [PT.toCloseds, Opens.coe_compl, compl_inter_nonempty_iff, IsIrreducible.toPTOpens_toFun]
  contrapose
  exact subset_toCloseds_apply_compl_iff u.isOpen

lemma toCloseds_injective (X : Type*) [TopologicalSpace X] : (PT.toCloseds (X := X)).Injective := by
  intro f g h
  rw [←toPTOpens_toCloseds f, ←toPTOpens_toCloseds g]
  congr

@[simp]
lemma toCloseds_toPTOpens {X : Type*} [TopologicalSpace X] {s : Set X} (h : IsIrreducible s) :
    h.toPTOpens.toCloseds = Closeds.closure s := by
  ext x
  simp only [PT.toCloseds, IsIrreducible.toPTOpens_toFun, Opens.coe_compl, Opens.coe_sSup,
    mem_ofPred_eq, compl_iUnion, mem_iInter, mem_compl_iff, SetLike.mem_coe, Closeds.coe_closure,
    mem_closure_iff, not_imp_not]
  refine ⟨fun h u hu hx => ?_, fun h ⟨u, hu⟩ hx => ?_⟩
  · grind [Opens.coe_mk, h ⟨u, hu⟩ hx]
  · grind [Opens.coe_mk,h u hu hx]

@[simps]
def irreducibleClosedEquiv (X : Type*) [TopologicalSpace X] :
    IrreducibleCloseds X ≃ PT (Opens X) where
  toFun | ⟨s, hirred, _⟩ => hirred.toPTOpens
  invFun x := ⟨x.toCloseds, x.isIrreducible_toCloseds, x.toCloseds.isClosed⟩
  left_inv := by
    intro ⟨s, hi, hc⟩
    simp
  right_inv := toPTOpens_toCloseds

lemma toPT_singleton {X : Type*} [TopologicalSpace X] (x : X) :
    (isIrreducible_singleton (x := x)).toPTOpens = localePointOfSpacePoint X x := by
  ext u; simp

theorem localePointOfSpacePoint_surjective (X : Type*) [TopologicalSpace X] [QuasiSober X] :
    (localePointOfSpacePoint X).Surjective := by
  intro y
  refine ⟨y.isIrreducible_toCloseds.genericPoint, toCloseds_injective X <| SetLike.coe_injective ?_⟩
  simp [← toPT_singleton, y.toCloseds.isClosed.closure_eq]

lemma isHomeomorph_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] [T0Space X]
    [QuasiSober X] : IsHomeomorph (localePointOfSpacePoint X) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_localePointOfSpacePoint X, localePointOfSpacePoint_surjective X⟩

noncomputable def homeomorphPtOpens (X : Type*) [TopologicalSpace X] [T0Space X] [QuasiSober X] :
    X ≃ₜ PT (Opens X) := (isHomeomorph_localePointOfSpacePoint X).homeomorph

end PT

open TopCat PT ConcreteCategory

def homEquivFrameHom (α β : Type u) [Order.Frame α] [Order.Frame β] :
    (Locale.of α ⟶ Locale.of β) ≃ FrameHom β α where
  toFun f := hom f.unop
  invFun f := (Frm.ofHom f).op

def continuousMapPTEquivFrameHomOpens (X : Type u) [TopologicalSpace X] (L : Type u)
    [Order.Frame L] : C(X, PT L) ≃ FrameHom L (Opens X) :=
  (Hom.equivContinuousMap ↧X ↧(PT L)).symm.trans <|
    (adjunctionTopToLocalePT.homEquiv ↧X _).symm.trans <| homEquivFrameHom _ _

noncomputable def continuousMapEquivFrameHom {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] : C(X, Y) ≃ FrameHom (Opens Y) (Opens X) :=
  (Homeomorph.refl X).continuousMapCongr (homeomorphPtOpens Y) |>.trans <|
    continuousMapPTEquivFrameHomOpens X (Opens Y)

lemma continuousMapEquivFrameHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space Y] [QuasiSober Y] (f : C(X, Y)) : continuousMapEquivFrameHom f = Opens.comap f := rfl

end Locale
