import Mathlib.CategoryTheory.Monad.Adjunction

namespace CategoryTheory

universe u v

namespace Monad

variable {C : Type u} [Category.{v} C] (T : Monad C)

@[simps]
def isoMu [IsIso T.μ] (X : C) : T.obj (T.obj X) ≅ T.obj X where
  hom := T.μ.app X
  inv := T.η.app (T.obj X)
  hom_inv_id := by simp [← (asIso <| T.μ.app X).cancel_iso_hom_right]

theorem isoMu_inv' [IsIso T.μ] (X : C) : (T.isoMu X).inv = T.map (T.η.app X) := by
  simp [← (T.isoMu X).cancel_iso_hom_right]

@[simp]
theorem map_eta_eq_eta [IsIso T.μ] (X : C) : T.map (T.η.app X) = T.η.app (T.obj X) :=
    (T.isoMu_inv' X).symm.trans (T.isoMu_inv X)

instance [IsIso T.μ] (X : C) : IsIso (T.η.app <| T.obj X) :=
    inferInstanceAs <| IsIso (T.isoMu X).inv

instance [IsIso T.μ] (X : C) : IsIso (T.map <| T.η.app X) := by
  rw [map_eta_eq_eta]
  infer_instance

@[reassoc (attr := simp)] lemma Algebra.a_comp_eta_app {T : Monad C} [IsIso T.μ] (X : T.Algebra) :
    X.a ≫ T.η.app X.A = 𝟙 _ := by
  simp [T.unit_naturality, ← map_eta_eq_eta, ← T.map_comp, X.unit]

@[simps]
def Algebra.aIso {T : Monad C} [IsIso T.μ] (X : T.Algebra) : T.obj X.A ≅ X.A where
  hom := X.a
  inv := T.η.app X.A
  inv_hom_id := X.unit

def Algebra.isoFree {T : Monad C} [IsIso T.μ] (X : T.Algebra) : T.free.obj X.A ≅ X :=
  Algebra.isoMk X.aIso X.assoc.symm

def Algebra.unique {T : Monad C} [IsIso T.μ] {X X' : T.Algebra} (h : X.A ≅ X'.A) : X ≅ X' :=
  X.isoFree.symm ≪≫ T.free.mapIso h ≪≫ X'.isoFree

lemma etaIso {T : Monad C} [IsIso T.μ] {X : C} (h : X ≅ T.obj X) : IsIso (T.η.app X) := by
  simp [h.inv_comp_eq.mp <| T.η.naturality h.inv, T.map_isIso]

@[simps]
def algebraOfSplitMonoEta {T : Monad C} [IsIso T.μ] {X : C} (h : SplitMono (T.η.app X)) :
    T.Algebra where
  A := X
  a := h.retraction
  assoc := by simp [← (T.isoMu X).symm.cancel_iso_hom_left, ← T.unit_naturality_assoc]

@[simps]
def homAlgebraOfHom {T : Monad C} [IsIso T.μ] {X Y : T.Algebra} (f : X.A ⟶ Y.A) : X ⟶ Y where
  f := f
  h := by
    simp_rw [← Y.aIso.symm.cancel_iso_hom_right, Iso.symm_hom, Algebra.aIso_inv, Category.assoc,
      Algebra.a_comp_eta_app, T.unit_naturality, Category.comp_id, Functor.id_obj,
      Algebra.a_comp_eta_app_assoc]

instance full_forget [IsIso T.μ] : T.forget.Full where
  map_surjective f := ⟨homAlgebraOfHom f, homAlgebraOfHom_f f⟩

instance reflective_forget [IsIso T.μ] : Reflective T.forget where
  L := T.free
  adj := T.adj

end Monad

end CategoryTheory
