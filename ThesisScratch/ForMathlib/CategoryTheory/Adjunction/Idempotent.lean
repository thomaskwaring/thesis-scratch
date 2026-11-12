import Mathlib.CategoryTheory.Adjunction.Basic
import ThesisScratch.ForMathlib.CategoryTheory.Monad.Idempotent

namespace CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {L : C ⥤ D} {R : D ⥤ C}

namespace Adjunction

class Idempotent (adj : L ⊣ R) where
  /-- `ε (L X) ≫ L (η X) = id` -/
  left_inv_triangle_components (X : C) :
    adj.counit.app (L.obj X) ≫ L.map (adj.unit.app X) = 𝟙 (L.obj <| R.obj <| L.obj X)

open Idempotent CategoryTheory.Functor

variable (adj : L ⊣ R)

attribute [reassoc (attr := simp)] left_inv_triangle_components

@[simps]
def leftTriangleComponentIso [Idempotent adj] (X : C) : L.obj X ≅ L.obj (R.obj (L.obj X)) where
  hom := L.map (adj.unit.app X)
  inv := adj.counit.app (L.obj X)

instance [Idempotent adj] (X : C) : IsIso (L.map (adj.unit.app X)) :=
    inferInstanceAs (IsIso (adj.leftTriangleComponentIso X).hom)

instance [Idempotent adj] (X : C) : IsIso (adj.counit.app (L.obj X)) :=
  inferInstanceAs (IsIso (adj.leftTriangleComponentIso X).inv)

@[simps!]
def leftTriangleIso [Idempotent adj] : L ≅ L ⋙ R ⋙ L := by
  refine L.leftUnitor.symm ≪≫ NatIso.ofComponents adj.leftTriangleComponentIso ?_
  intro X Y f
  simpa using (Functor.whiskerRight adj.unit L).naturality f

theorem leftTriangleIso_hom [Idempotent adj] :
    adj.leftTriangleIso.hom = L.leftUnitor.inv ≫ whiskerRight adj.unit L := by
  ext; simp

theorem leftTriangleIso_inv [Idempotent adj] :
    adj.leftTriangleIso.inv = whiskerLeft L adj.counit ≫ L.leftUnitor.hom := by
  ext; simp

@[simps!]
def leftWhiskerTriangleIso [Idempotent adj] (X : C) :
    R.obj (L.obj X) ≅ R.obj (L.obj (R.obj (L.obj X))) := R.mapIso (adj.leftTriangleComponentIso X)

-- name?
lemma whiskerAppEq [Idempotent adj] (X : C) :
    R.map (L.map <| adj.unit.app X) = adj.unit.app (R.obj <| L.obj X) := by
  simp [← (adj.leftWhiskerTriangleIso X).symm.cancel_iso_hom_right, ← R.map_comp]

end Adjunction

end CategoryTheory
