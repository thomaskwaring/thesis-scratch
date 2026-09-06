import Mathlib.CategoryTheory.Types.Basic
import ThesisScratch.ForMathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Data.Set.Functor
import Mathlib.CategoryTheory.Monad.Types
import Mathlib.CategoryTheory.ConcreteCategory.Basic
-- import Mathlib.CategoryTheory.Category.RelCat
import ThesisScratch.ForMathlib.CategoryTheory.RelCat

namespace CategoryTheory

open ConcreteCategory TypeCat RelCat' Hom SetRel

universe u

variable {X Y : Type u}

attribute [local instance] Set.monad

section attempt2

-- attribute [local instance] Set.monad

-- def covSet : CategoryTheory.Monad (Type u) := ofTypeMonad Set

-- lemma covSet_obj (X : Type u) : covSet.obj X = Set X := rfl

-- @[simp] lemma covSet_map (f : X ⟶ Y) : covSet.map f = ↾(f '' ·) := rfl

-- -- lemma covSet_μ_app (X : Type u) : covSet.μ.app X = ↾(joinM) := ofTypeMonad_μ_app Set X

-- @[simp] lemma covSet_μ_app (X : Type u) : covSet.μ.app X = ↾(⋃₀ ·) := by
--   ext (u : Set (Set X))
--   exact Set.sUnion_eq_biUnion.symm

-- lemma covSet_η_app_apply {x : X} : covSet.η.app X x = ({x} : Set X) := rfl

-- lemma covSet_μ_app_apply (u : Set (Set X)) : covSet.μ.app X u = ⋃₀ u :=
--   Set.sUnion_eq_biUnion.symm

-- def covSetToSet {X : Type u} (s : covSet.obj X) : Set X := s

-- @[simp] lemma covSetToSet_map (f : X ⟶ Y) (s : covSet.obj X) :
--     covSetToSet (covSet.map f s) = f '' (covSetToSet s) := rfl

-- @[simp] lemma covSetToSet_η_app (x : X) : covSetToSet (covSet.η.app X x) = {x} := rfl

-- @[simp] lemma covSetToSet_μ_app (u : covSet.obj (covSet.obj X)) :
--     covSetToSet (covSet.μ.app X u) = ⋃ s ∈ covSetToSet u, covSetToSet s := rfl

-- def toRelCat' : Kleisli covSet.{u} ⥤ RelCat'.{u} where
--   obj X := ⟨X.of⟩
--   map {X Y} f := ofRel <| {(x, y) : X.of × Y.of | y ∈ covSetToSet (f.of x)}
--   map_id X := by
--     ext ⟨x, y⟩
--     simp
--     -- rw [covSetToSet_η_app]
--     -- grind
--   map_comp {X Y Z} f g := by
--     ext ⟨x : X.of, z : Z.of⟩
--     sorry
--     -- simp?
--     -- rw [CategoryTheory.hom_comp]
--     -- rw [covSet_map, ofTypeMonad_μ_app]
--     -- rw [covSet_μ_app_apply (X := Z.of)]

end attempt2

section attempt1

-- def toSetCovSetApply {X : Type u} (s : covSet.obj X) : Set X := s

-- @[simp] lemma toSetCovSetApply_map (f : X ⟶ Y) (s : covSet.obj X) :
--     toSetCovSetApply (covSet.map f s) = f '' (toSetCovSetApply s) := rfl

-- @[simp] lemma toSetCovSetApply_η_app (x : X) : toSetCovSetApply (covSet.η.app X x) = {x} := rfl

-- @[simp] lemma toSetCovSetApply_μ_app (u : covSet.obj (covSet.obj X)) :
--     toSetCovSetApply (covSet.μ.app X u) = ⋃ s ∈ toSetCovSetApply u, toSetCovSetApply s := rfl

-- def coeRelCat (X : Type u) : RelCat.{u} := X

-- def uncoeRelCat {X : Type u} (x : coeRelCat X) : X := x

-- def toRelCat : Kleisli covSet.{u} ⥤ RelCat.{u} where
--   obj X := coeRelCat X.of
--   map {X Y} f := Hom.ofRel <|
--     {⟨x, y⟩ : coeRelCat X.of × coeRelCat Y.of | uncoeRelCat y ∈ toSetCovSetApply (f.of <| uncoeRelCat x)}
--   map_id X := by
--     ext ⟨x, x'⟩
--     simp_rw [Kleisli.category_id_of, Set.mem_ofPred_eq, Hom.rel_id]
--     rw [toSetCovSetApply_η_app, Set.mem_singleton_iff, Eq.comm]
--     rfl
--   map_comp := sorry
    -- simp [uncoeRelCat, Set.mem_singleton_iff]

-- def Kleisli.Hom.toFun {X Y : Kleisli covSet} (f : X ⟶ Y) : Fun X.of (covSet.obj Y.of) :=
--   ConcreteCategory.hom f.of

-- @[simp]
-- lemma Kleisli.Hom.toFun_id (X : Kleisli covSet) :
--     (𝟙 X : X ⟶ X).toFun = ⟨fun x ↦ ({x} : Set X.of)⟩ := rfl

-- lemma Kleisli.Hom.toFun_comp {X Y Z : Kleisli covSet} (f : X ⟶ Y) (g : Y ⟶ Z) :
--     (f ≫ g).toFun = sorry := by
--   simp [toFun]
--   ext x
  -- simp only [covSet_obj, toFun, category_comp_of, Fun.toFun_apply, Function.const_apply]

-- def Kleisli.Hom.imSet {X Y : Kleisli covSet} (f : X ⟶ Y) (x : X.of) : Set Y.of := f.toFun x

-- @[simp]
-- lemma Kleisli.Hom.imSet_id_apply {X : Kleisli covSet} (x : X.of) :
--     (𝟙 X : X ⟶ X).imSet x = {x} := rfl

-- lemma Kleisli.Hom.imSet_comp_apply {X Y Z : Kleisli covSet} (f : X ⟶ Y) (g : Y ⟶ Z)
--     (x : X.of) :
--     (f ≫ g).imSet x = ⋃ y ∈ f.imSet x, g.imSet y := by
--   simp [imSet, toFun]
--   rw [ConcreteCategory.comp_apply]
  -- change ⋃ s ∈ ((f.of ≫ covSet.map g.of) x : Set (Set Z.of)), s = ⋃ y ∈ f.imSet x, g.imSet y



-- def toSetRel {X Y : Kleisli covSet} (f : X ⟶ Y) : SetRel X.of Y.of :=
--   {(x, y) : X.of × Y.of | y ∈ (f.of.hom x : Set Y.of)}

-- def toRelCat : Kleisli covSet ⥤ RelCat where
--   obj X := X.of
--   map {X Y} f := Hom.ofRel {⟨x, y⟩ : X.of × Y.of | y ∈ f.imSet x}
--   map_id X := by
--     ext ⟨x, x'⟩
--     simp only [Kleisli.Hom.imSet_id_apply, Set.mem_singleton_iff, Set.mem_ofPred_eq]
--     rw [Eq.comm, Iff.comm]
--     exact RelCat.Hom.rel_id_apply₂ x x'
--   map_comp {X Y Z} f g := by
--     ext ⟨x, z⟩
--     simp

end attempt1


section old

-- @[simps]
-- def covariantSet : Type u ⥤ Type u where
--   obj X := Set X
--   map f := ↾(f.hom '' ·)

-- @[simp]
-- lemma covariantSet_map_ofHom_apply (f : X → Y) (s : Set X) :
--   (covariantSet.map (↾f) |>.hom s) = f '' s := rfl

-- protected def singleton : 𝟭 _ ⟶ covariantSet.{u} where
--   app X := ↾(fun x ↦ ({x} : Set X))
--   naturality {X Y} f := by ext; exact Set.image_singleton.symm

-- protected def union : covariantSet.{u} ⋙ covariantSet.{u} ⟶ covariantSet.{u} where
--   app X := ↾(⋃₀ ·)
--   naturality {X Y} f := by ext; exact Set.image_sUnion.symm

-- def covariantSetMonad : CategoryTheory.Monad (Type u) where
--   __ := covariantSet
--   η := TypeCat.singleton
--   μ := TypeCat.union
--   assoc X := by ext U; exact Set.sUnion_assoc U
--   left_unit X := by ext u; exact Set.sUnion_singleton u
--   right_unit X := by
--     ext (u : Set X)
--     change ⋃₀ ((fun x ↦ ({x} : Set X)) '' u) = u
--     simp

end old

end CategoryTheory
