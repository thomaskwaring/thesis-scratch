import ThesisScratch.ForCslib.CPL.Defs
import Mathlib.Data.Finset.Lattice.Fold

namespace CPL

universe u v

open Set Finset

variable {Atom : Type u}

open Prp

inductive IProof : {α β : Type v} → (α → Prp Atom) → (β → Prp Atom) → Type _ where
  | ax (l : α → Prp Atom) (r : β → Prp Atom) (A : Prp Atom) :
      IProof (Option.rec A l) (Option.rec A r)
  | str {l : α → Prp Atom} {l' : α' → Prp Atom} {r : β → Prp Atom} {r' : β' → Prp Atom}
      {el : α → α'} {er : β → β'} (hl : l' ∘ el = l) (hr : r' ∘ er = r) :
      IProof l r → IProof l' r'
  | negL {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom} :
      IProof l (Option.rec A r) → IProof (Option.rec (¬ A) l) r
  | negR {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom} :
      IProof (Option.rec A l) r → IProof l (Option.rec (¬ A) r)
  | andL {l : α → Prp Atom} {r : β → Prp Atom} {A B : Prp Atom} :
      IProof (Option.rec A <| Option.rec B l) r → IProof (Option.rec (A ∧ B) l) r
  | andr {l : α → Prp Atom} {r : β → Prp Atom} {A B : Prp Atom} :
      IProof l (Option.rec A r) → IProof l (Option.rec B r) → IProof l (Option.rec (A ∧ B) r)

def_wanted IProof.cut {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom}
     (π : IProof l (Option.rec A r)) (ρ : IProof (Option.rec A l) r) : IProof l r

variable {α β : Type*}

structure IConc (α Atom : Type*) where
  p : α → Prp Atom
  dom : Set α

instance : CoeFun (IConc α Atom) (fun _ ↦ α → Prp Atom) where
  coe := IConc.p

def IConc.erase [DecidableEq α] (f : IConc α Atom) (x : α) : IConc α Atom where
  p := f.p
  dom := f.dom \ {x}

def IConc.update [DecidableEq α] (f : IConc α Atom) (x : α) (A : Prp Atom) : IConc α Atom where
  p := Function.update f.p x A
  dom := f.dom

instance : Setoid (IConc α Atom) where
  r f g := f.dom = g.dom ∧ ∀ x ∈ f.dom, f x = g x
  iseqv := by constructor <;> grind

lemma _root_.HasEquiv.Equiv.dom_eq {f g : IConc α Atom} (h : f ≈ g) : f.dom = g.dom := h.1

lemma _root_.HasEquiv.Equiv.apply_eq {f g : IConc α Atom} (h : f ≈ g) {x : α} (hx : x ∈ f.dom) :
    f x = g x := h.2 x hx

lemma _root_.HasEquiv.Equiv.apply_eq' {f g : IConc α Atom} (h : f ≈ g) {x : α} (hx : x ∈ g.dom) :
    f x = g x := h.2 x (h.dom_eq ▸ hx)

instance : HasSubset (IConc α Atom) where
  Subset f g := f.dom ⊆ g.dom ∧ ∀ x ∈ f.dom, f x = g x

instance : Std.Refl (· ⊆ · : IConc α Atom → IConc α Atom → Prop) where
  refl c := ⟨refl c.dom, fun _ _ ↦ rfl⟩

instance : IsTrans _ (· ⊆ · : IConc α Atom → IConc α Atom → Prop) where
  trans _ _ _ h h' := ⟨h.1.trans h'.1, fun x hx ↦ (h.2 x hx).trans <| h'.2 x (h.1 hx)⟩

lemma _root_.HasSubset.Subset.dom_subset {f g : IConc α Atom} (h : f ⊆ g) : f.dom ⊆ g.dom := h.1

lemma _root_.HasSubset.Subset.apply_eq {f g : IConc α Atom} (h : f ⊆ g) {x : α} (hx : x ∈ f.dom) :
    f x = g x := h.2 x hx

lemma _root_.HasEquiv.Equiv.subset {f g : IConc α Atom} (h : f ≈ g) : f ⊆ g :=
    ⟨h.dom_eq.subset, @h.apply_eq⟩

lemma equiv_iff {f g : IConc α Atom} : f ≈ g ↔ f ⊆ g ∧ g ⊆ f := by
  refine ⟨fun h ↦ ⟨h.subset, (symm h).subset⟩, fun h ↦ ⟨h.1.1.antisymm h.2.1, h.1.2⟩⟩

def IConc.comap (c : IConc β Atom) (f : α → β) : IConc α Atom where
  p := c.p ∘ f
  dom := f ⁻¹' c.dom

lemma subset_comap_iff {c : IConc α Atom} {d : IConc β Atom} {f : α → β} :
    c ⊆ d.comap f ↔ c.dom.MapsTo f d.dom ∧ c.dom.EqOn c.p (d.p ∘ f) := by rfl

lemma _root_.HasSubset.Subset.apply_mem_dom_of_comap {c : IConc α Atom} {d : IConc β Atom}
    {f : α → β} (h : c ⊆ d.comap f) {x : α} (hx : x ∈ c.dom) : f x ∈ d.dom :=
  (subset_comap_iff.mp h).1 hx

lemma _root_.HasSubset.Subset.apply_eq_of_comap {c : IConc α Atom} {d : IConc β Atom}
    {f : α → β} (h : c ⊆ d.comap f) {x : α} (hx : x ∈ c.dom) : c x = d (f x) :=
  (subset_comap_iff.mp h).2 hx

lemma comap_mono {c d : IConc β Atom} (h : c ⊆ d) (f : α → β) : c.comap f ⊆ d.comap f := by
  constructor
  · simpa [IConc.comap] using Set.preimage_mono h.dom_subset
  · intro x (hx : f x ∈ c.dom)
    simpa [IConc.comap] using h.apply_eq hx

lemma _root_.HasEquiv.Equiv.comap {c d : IConc β Atom} (h : c ≈ d) (f : α → β) :
    c.comap f ≈ d.comap f :=
  equiv_iff.mpr ⟨comap_mono h.subset f, comap_mono (symm h).subset f⟩

-- def IConc.insert [DecidableEq α] (c : IConc α Atom) (x : α) (A : Prp Atom) : IConc α Atom where
--   p := Function.update c.p x A
--   dom := c.dom ∪ {x}

def IConc.insert [DecidableEq α] (c : IConc α Atom) (x : α) : IConc α Atom where
  p := c.p
  dom := c.dom ∪ {x}

inductive IProof' [DecidableEq α] : IConc α Atom → IConc α Atom → Type _ where
  | ax {l r : IConc α Atom} {x y : α} (hx : x ∈ l.dom) (hy : y ∈ r.dom) (h : l x = r y) :
      IProof' l r
  | str {el er : α → α} {l l' r r' : IConc α Atom} (hl : l ⊆ l'.comap el) (hr : r ⊆ r'.comap er) :
      IProof' l r → IProof' l' r'
  | negL {l r : IConc α Atom} {x y : α} (hl : x ∈ l.dom) (hr : y ∉ r.dom) (h : l x = ¬ r y) :
      IProof' (l.erase x) (r.insert x) → IProof' l r
  | negR {l r : IConc α Atom} {x y : α} (hl : x ∉ l.dom) (hr : y ∈ r.dom) (h : r y = ¬ l x) :
      IProof' (l.insert x) (r.erase x) → IProof' l r
  | andL {l r : IConc α Atom} {x y z : α} (hx : x ∉ l.dom) (hy : y ∉ l.dom) (hz : z ∈ l.dom)
      (hne : x ≠ y) (heq : l z = (l x ∧ l y)) :
      IProof' (l.erase z |>.insert x |>.insert y) r → IProof' l r
  | andR {l r : IConc α Atom} {x y z : α} (hx : x ∉ l.dom) (hy : y ∉ l.dom) (hz : z ∈ l.dom)
      (h : r z = (r x ∧ r y)) :
      IProof' l (r.erase z |>.insert x) → IProof' l (r.erase z |>.insert x) → IProof' l r

-- def_wanted IProof'.cut [DecidableEq α] {l r : IConc α Atom} {x y : α} (hx : x ∈ l.dom)
--     (hy : y ∈ r.dom) (h : l x = r y) :
--     IProof' (l.erase x) r → IProof' l (r.erase y) → IProof' (l.erase x) (r.erase y)

-- def IProof'.weak [DecidableEq α] :
--     {l l' r r' : IConc α Atom} → (hl : l ⊆ l') → (hr : r ⊆ r') →  IProof' l r → IProof' l' r'
--   | _, _, _, _, hl, hr, ax hx hy h => ax (hl.dom_subset hx) (hr.dom_subset hy) <| by
--       rwa [← hl.apply_eq hx, ← hr.apply_eq hy]
--   | l, l', r, r', hl, hr, @str _ _ _ el er le _ re _ hel her π =>
--       (π.weak (_root_.trans hel <| comap_mono hl el) (_root_.trans her <| comap_mono hr er)).str
--         (refl _) (refl _)
--   | l, l', r, r', hl, hr, negL hx hy h π => by
--     -- have := π.



end CPL
