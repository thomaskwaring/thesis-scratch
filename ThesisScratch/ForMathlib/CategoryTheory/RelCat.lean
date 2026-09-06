import Mathlib.Data.Rel
import Mathlib.CategoryTheory.Types.Basic

namespace CategoryTheory

open SetRel

universe u

@[ext]
structure RelCat' : Type (u + 1) where
  of : Type u

namespace RelCat'

@[simp] lemma mk_of (X : RelCat') : RelCat'.mk X.of = X := rfl
lemma of_mk (X : Type u) : (RelCat'.mk X).of = X := rfl

structure Hom (X Y : RelCat') : Type u where
  ofRel :: (
    rel : SetRel X.of Y.of
  )

open Hom

instance instLargeCategory : LargeCategory RelCat' where
  Hom := Hom
  id _ := .ofRel .id
  comp f g := .ofRel <| f.rel ○ g.rel

variable {X Y Z : RelCat'}

namespace Hom

@[ext] lemma ext {f g : X ⟶ Y} (h : f.rel = g.rel) : f = g := by cases f; cases g; congr

@[simp] protected lemma rel_id (X : RelCat') : rel (𝟙 X) = SetRel.id := rfl

@[simp] protected lemma rel_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).rel = f.rel.comp g.rel := rfl

theorem rel_id_apply₂ (x y : X.of) : x ~[rel (𝟙 X)] y ↔ x = y := .rfl

theorem rel_comp_apply₂ (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.of) (z : Z.of) :
    x ~[(f ≫ g).rel] z ↔ ∃ y, x ~[f.rel] y ∧ y ~[g.rel] z := .rfl

end Hom

end RelCat'

end CategoryTheory
