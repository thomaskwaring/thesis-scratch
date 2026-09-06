import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.CategoryTheory.Monad.Adjunction

namespace CategoryTheory

open Adjunction CategoryTheory.Functor Kleisli Kleisli.Adjunction Category

universe v u v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

namespace Adjunction

@[simp] lemma toMonad_obj : adj.toMonad.obj = (L ⋙ R).obj := rfl
@[simp] lemma toMonad_map {X Y : C} : adj.toMonad.map (X := X) (Y := Y) = (L ⋙ R).map := rfl

attribute [local implicit_reducible] toMonad fromKleisli toKleisli

attribute [local simp] homEquiv_symm_apply

@[simps, implicit_reducible]
def kComparison : Kleisli adj.toMonad ⥤ D where
  obj X := L.obj X.of
  map {X Y} f := adj.homEquiv X.of (L.obj Y.of) |>.symm f.of

@[simp]
private lemma toKleisli_obj (T : Monad C) (X : C) : (toKleisli T).obj X = .mk T X := rfl

def kComparisonCompRIsoFromKleisli :
    adj.kComparison ⋙ R ≅ fromKleisli adj.toMonad where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

def toKleisliCompKComparisonIsoL :
    toKleisli adj.toMonad ⋙ adj.kComparison ≅ L where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

instance : Faithful adj.kComparison where
  map_injective {X Y} f g h := by
    ext
    exact (adj.homEquiv X.of (L.obj Y.of)).symm.injective h

instance : Full adj.kComparison where
  map_surjective {X Y} f := by
    use ⟨adj.homEquiv X.of (L.obj Y.of) f⟩
    simp

-- def comparisonIso (T : Monad C) :
--   T.adj.kComparison ≅ Monad.comparison (Kleisli.Adjunction.adj T) where

end Adjunction

namespace Kleisli

-- attribute [local implicit_reducible] fromKleisli toKleisli

@[simp]
lemma Adjunction.counit_adj (T : Monad C) (X : Kleisli T) :
    ((Adjunction.adj T).counit.app X).of = 𝟙 (T.obj X.of) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
protected def Adjunction.kAdjToMonadIso (T : Monad C) : (Kleisli.Adjunction.adj T).toMonad ≅ T where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

@[implicit_reducible, simps]
def ofMonadHom {T₁ T₂ : Monad C} (t : T₁ ⟶ T₂) : Kleisli T₁ ⥤ Kleisli T₂ where
  obj X := .mk T₂ X.of
  map {X Y} f := .mk <| f.of ≫ t.app Y.of

@[simps (rhsMd := .default)]
def ofMonadHom.id (T : Monad C) : ofMonadHom (𝟙 T) ≅ 𝟭 (Kleisli T) :=
  NatIso.ofComponents <| fun _ => Iso.refl _

@[simps (rhsMd := .default)]
def ofMonadHom.comp {T₁ T₂ T₃ : Monad C} (t₁ : T₁ ⟶ T₂) (t₂ : T₂ ⟶ T₃) :
    ofMonadHom (t₁ ≫ t₂) ≅ ofMonadHom t₁ ⋙ ofMonadHom t₂ :=
  NatIso.ofComponents <| fun _ => Iso.refl _

@[simps (rhsMd := .default)]
def ofMonadHom.eqToIso {T₁ T₂ : Monad C} {t₁ t₂ : T₁ ⟶ T₂} (h : t₁ = t₂) :
    ofMonadHom t₁ ≅ ofMonadHom t₂ :=
  NatIso.ofComponents <| fun _ => Iso.refl _

def ofMonadIso {T₁ T₂ : Monad C} (e : T₁ ≅ T₂) : Kleisli T₁ ≌ Kleisli T₂ where
  functor := ofMonadHom e.hom
  inverse := ofMonadHom e.inv
  unitIso := (ofMonadHom.id T₁).symm ≪≫
    ofMonadHom.eqToIso e.hom_inv_id.symm ≪≫ ofMonadHom.comp e.hom e.inv
  counitIso := (ofMonadHom.comp e.inv e.hom).symm ≪≫
    ofMonadHom.eqToIso e.inv_hom_id ≪≫ ofMonadHom.id T₂

-- def kleisliAlg (T : Monad C) : Kleisli T ⥤ T.Algebra :=
--   (ofMonadIso (Adjunction.adjToMonadIso T)).inverse ⋙ T.adj.kComparison

-- def kleisliAlg' (T : Monad C) : Kleisli T ⥤ T.Algebra :=
--   Monad.comparison (Kleisli.Adjunction.adj T) ⋙
--     (Monad.algebraEquivOfIsoMonads (Adjunction.kAdjToMonadIso T)).functor

-- set_option backward.defeqAttrib.useBackward true in
-- set_option backward.isDefEq.respectTransparency false in
-- def kComparisonComparison (T : Monad C) :
--     (ofMonadIso (Adjunction.adjToMonadIso T)).inverse ⋙ T.adj.kComparison ≅
--     Monad.comparison (Kleisli.Adjunction.adj T) ⋙
--       (Monad.algebraEquivOfIsoMonads (Adjunction.kAdjToMonadIso T)).functor where
--   hom := {app X := by simp
--   }



end CategoryTheory.Kleisli
