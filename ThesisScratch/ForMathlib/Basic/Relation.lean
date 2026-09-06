-- import ThesisScratch.ForMathlib.Partition.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Relator

open Relation Function Part Set Relator

variable {α β : Type*} {r : α → β → Prop} {a x : α} {b y : β}

namespace Relation

def dom (r : α → β → Prop) : Set α := {a | ∃ b, r a b}

def cod (r : α → β → Prop) : Set β := {b | ∃ a, r a b}

lemma mem_dom_left (h : r x y) : x ∈ dom r := ⟨y, h⟩

lemma dom_mono {s r : α → β → Prop} (h : s ≤ r) : dom s ⊆ dom r := by
  intro x ⟨y, hy⟩
  exact ⟨y, h _ _ hy⟩

@[simp] lemma dom_swap : dom (swap r) = cod r := rfl

lemma mem_cod_right (h : r x y) : y ∈ cod r := ⟨x, h⟩

lemma cod_mono {s r : α → β → Prop} (h : s ≤ r) : cod s ⊆ cod r := by
  intro y ⟨x, hx⟩
  exact ⟨x, h _ _ hx⟩

@[simp] lemma cod_swap : cod (swap r) = dom r := rfl

def im (r : α → β → Prop) (a : α) : Set β := {b | r a b}

def coim (r : α → β → Prop) (b : β) : Set α := {a | r a b}

lemma im_mono {s r : α → β → Prop} (h : s ≤ r) {x : α} : im s x ⊆ im r x :=
  fun _ h' => h _ _ h'

lemma im_nonempty_iff {r : α → β → Prop} {x : α} : (im r x).Nonempty ↔ x ∈ dom r := Iff.rfl

lemma im_eq_empty_iff : im r x = ∅ ↔ x ∉ dom r := by
  contrapose!
  exact im_nonempty_iff

@[simp] lemma im_swap : im (swap r) y = coim r y := rfl

lemma coim_mono {s r : α → β → Prop} (h : s ≤ r) {y : β} : coim s y ⊆ coim r y :=
  fun _ h' => h _ _ h'

lemma coim_nonempty_iff {r : α → β → Prop} {y : β} : (coim r y).Nonempty ↔ y ∈ cod r := Iff.rfl

lemma coim_eq_empty_iff {r : α → β → Prop} {y : β} : coim r y = ∅ ↔ y ∉ cod r := by
  contrapose!
  exact coim_nonempty_iff

@[simp] lemma coim_swap : coim (swap r) x = im r x := rfl

variable {r : α → α → Prop} {a b c x y : α}

lemma mem_dom_right [Std.Symm r] {x y : α} (hxy : r x y) : y ∈ dom r := ⟨x, symm hxy⟩

lemma mem_cod_left [Std.Symm r] {x y : α} (hxy : r x y) : x ∈ cod r := ⟨y, symm hxy⟩

lemma dom_eq_cod_of_symm [Std.Symm r] : dom r = cod r := by grind [Std.Symm, dom, cod]

lemma im_eq_coim_of_symm [Std.Symm r] : im r x = coim r x := by
  ext y
  constructor <;> exact symm

lemma SymmGen.self_le : r ≤ SymmGen r := fun _ _ => Or.inl

lemma dom_symmGen : dom (SymmGen r) = dom r ∪ cod r := by
  ext x
  constructor
  · rintro ⟨y, (h | h)⟩
    · exact mem_union_left _ ⟨y, h⟩
    · exact mem_union_right _ ⟨y, h⟩
  · rintro (⟨y, h⟩ | ⟨y, h⟩) <;> use y
    · exact Or.inl h
    · exact Or.inr h

lemma TransGen.self_le : r ≤ TransGen r := fun _ _ => single

@[simp] lemma dom_transGen : dom (TransGen r) = dom r := by
  refine Subset.antisymm ?_ (dom_mono TransGen.self_le)
  intro x ⟨y, h⟩
  induction h using TransGen.head_induction_on with
  | single h => exact ⟨y, h⟩
  | @head _ y h => exact ⟨y, h⟩

class PER (r : α → α → Prop) extends Std.Symm r, IsTrans α r

def PERGen (r : α → α → Prop) : α → α → Prop := TransGen (SymmGen r)

namespace PERGen

lemma single (h : r a b) : PERGen r a b := TransGen.single (.inl h)

lemma single_symm (h : r b a) : PERGen r a b := TransGen.single (.inr h)

lemma tail (h : PERGen r a b) (h' : r b c) : PERGen r a c := TransGen.tail h (.inl h')

lemma tail_symm (h : PERGen r a b) (h' : r c b) : PERGen r a c := TransGen.tail h (.inr h')

lemma head (h : r a b) (h' : PERGen r b c) : PERGen r a c := TransGen.head (.inl h) h'

lemma head_symm (h : r b a) (h' : PERGen r b c) : PERGen r a c := TransGen.head (.inr h) h'

protected theorem induction {motive : (b : α) → PERGen r a b → Prop}
    (single : ∀ {b : α} (h : r a b), motive b (single h))
    (single_symm : ∀ {b : α} (h : r b a), motive b (single_symm h))
    (tail : ∀ {b c : α} (h : PERGen r a b) (h' : r b c), motive b h → motive c (h.tail h'))
    (tail_symm : ∀ {b c : α} (h : PERGen r a b) (h' : r c b),
      motive b h → motive c (h.tail_symm h'))
    (h : PERGen r a b) : motive b h := by
  induction h with
  | single h =>
    rcases h with (h | h)
    · exact single h
    · exact single_symm h
  | tail h h' ih =>
    rcases h' with (h' | h')
    · exact tail h h' ih
    · exact tail_symm h h' ih

instance : IsTrans α (PERGen r) := inferInstanceAs (IsTrans α (TransGen (SymmGen r)))

protected lemma trans (h : PERGen r a b) (h' : PERGen r b c) : PERGen r a c := _root_.trans h h'

instance : Std.Symm (PERGen r) where
  symm a b h := by
    induction h using PERGen.induction with
    | single h => exact single_symm h
    | single_symm h => exact single h
    | tail _ h' ih => exact head_symm h' ih
    | tail_symm _ h' ih => exact head h' ih

protected lemma symm (h : PERGen r a b) : PERGen r b a := symm h

lemma trans_symm (h : PERGen r a b) (h' : PERGen r c b) : PERGen r a c := h.trans h'.symm

lemma of_join : Join r x y → PERGen r x y
  | ⟨_, hx, hy⟩ => single hx |>.tail_symm hy

protected lemma minimal {r s : α → α → Prop} [PER s] (hle : r ≤ s) : PERGen r ≤ s := by
  intro x y h
  induction h using PERGen.induction with
  | single h => exact hle _ _ h
  | single_symm h => exact symm (hle _ _ h)
  | tail h h' ih => exact _root_.trans ih (hle _ _ h')
  | tail_symm h h' ih => exact _root_.trans ih (symm <| hle _ _ h')

lemma self_le : r ≤ PERGen r := fun _ _ => single

lemma swap : PERGen (Function.swap r) = PERGen r := by
  unfold PERGen
  congr 1
  exact symmGen_swap r

protected lemma dom : dom (PERGen r) = dom r ∪ cod r := by rw [PERGen, dom_transGen, dom_symmGen]

end PERGen

namespace PER

variable [PER r]

lemma mem_dom_iff (x : α) : x ∈ dom r ↔ r x x :=
  ⟨fun ⟨_, h⟩ => _root_.trans h (symm h), fun h => ⟨x, h⟩⟩

theorem equivalence_onFun_dom : Equivalence (onFun r (fun (x : dom r) => ↑x)) where
  refl := fun ⟨x, hx⟩ => mem_dom_iff x |>.mp hx
  symm := symm
  trans := _root_.trans

lemma mem_im_self : x ∈ im r x ↔ x ∈ dom r := by rw [mem_dom_iff]; rfl

lemma rel_of_mem_im_of_mem_im {x y z : α} (hy : y ∈ im r x) (hz : z ∈ im r x) : r y z :=
  _root_.trans (symm hy) hz

lemma rel_of_mem_inter_im {x y z : α} (hx : z ∈ im r x) (hy : z ∈ im r y) : r x y :=
  _root_.trans hx (symm hy)

lemma im_eq_of_rel {x y : α} (h : r x y) : im r y = im r x := by
  ext z
  exact ⟨trans h, rel_of_mem_im_of_mem_im h⟩

lemma im_disjoint_or_eq (r : α → α → Prop) [PER r] (x y : α) :
    Disjoint (im r x) (im r y) ∨ im r x = im r y := by
  by_cases r x y
  case pos h => exact Or.inr (im_eq_of_rel h).symm
  case neg h =>
    left
    rw [Set.disjoint_iff]
    intro z ⟨hx, hy⟩
    exact h <| rel_of_mem_inter_im hx hy

end PER

end Relation

namespace PFun

variable {f : α →. β} {x y : α}

protected def Ker (f : α →. β) : α → α → Prop := fun x y => ∃ b, b ∈ f x ∧ b ∈ f y

instance : PER f.Ker where
  symm _ _ := fun ⟨b, hx, hy⟩ => ⟨b, hy, hx⟩
  trans _ _ _ := by
    intro ⟨b, hx, hy⟩ ⟨c, hy', hz⟩
    obtain rfl : b = c := mem_unique hy hy'
    exact ⟨b, hx, hz⟩

lemma dom_ker : dom f.Ker = f.Dom := by
  ext x
  simp [PER.mem_dom_iff, PFun.Ker]

lemma ker_iff_of_mem_dom (hx : x ∈ f.Dom) : f.Ker x y ↔ f x = f y := by
  constructor
  · intro ⟨_, h, h'⟩
    exact mem_right_unique h h'
  · intro heq
    use (f x).get hx
    simpa [←heq] using get_mem hx

end PFun

namespace Relation

variable {α β : Type*} {s r : α → β → Prop}

lemma rightUnique_iff : RightUnique r ↔ Comp (swap r) r ≤ (· = ·) := by
  constructor
  · intro h y y' ⟨x, hy, hy'⟩
    exact h hy hy'
  · intro h x y y' hy hy'
    exact h y y' ⟨x, hy, hy'⟩

lemma leftTotal_iff : LeftTotal r ↔ (· = ·) ≤ Comp r (swap r) := by
  constructor
  · rintro h x _ rfl
    obtain ⟨y, hy⟩ := h x
    use y, hy, hy
  · intro h x
    obtain ⟨y, hy, -⟩ := h x x rfl
    use y, hy

lemma isTrans_iff {r : α → α → Prop} : IsTrans α r ↔ Comp r r ≤ r := by
  constructor
  · intro h x y ⟨z, hx, hy⟩
    exact _root_.trans hx hy
  · intro h
    constructor
    intro x y z hxy hyz
    exact h x z ⟨y, hxy, hyz⟩

lemma map_equiv_iff {α α' β β' : Type*} {r : α → β → Prop} {eα : α ≃ α'} {eβ : β ≃ β'} {x : α'}
    {y : β'} : Relation.Map r eα eβ x y ↔ r (eα.symm x) (eβ.symm y) := by
  grind [Relation.Map]

def Restrict {α β : Type*} (r : α → β → Prop) (s : Set α) (t : Set β) (x : α) (y : β) : Prop :=
  r x y ∧ x ∈ s ∧ y ∈ t

lemma restrict_rel {r : α → β → Prop} {s : Set α} {t : Set β} {x : α} {y : β}
    (h : Restrict r s t x y) : r x y := h.1

lemma restrict_left_mem {r : α → β → Prop} {s : Set α} {t : Set β} {x : α} {y : β}
    (h : Restrict r s t x y) : x ∈ s := h.2.1

lemma restrict_right_mem {r : α → β → Prop} {s : Set α} {t : Set β} {x : α} {y : β}
    (h : Restrict r s t x y) : y ∈ t := h.2.2

lemma restrict_iff_of_mem {r : α → β → Prop} {s : Set α} {t : Set β} {x : α} {y : β}
    (hx : x ∈ s) (hy : y ∈ t) : Restrict r s t x y ↔ r x y := by simp_all [Restrict]

end Relation
