import Mathlib.Tactic.Common
import Mathlib.Data.Set.Finite.Basic

open List

namespace CPL

inductive Prp (Atom : Type u) : Type u where
  | atom (x : Atom) : Prp Atom
  | or (A B : Prp Atom) : Prp Atom
  | not (A : Prp Atom) : Prp Atom
  deriving DecidableEq, Inhabited

variable {Atom : Type*}

namespace Prp

infixl:35 " ∨ " => Prp.or
notation:max "¬" A:45 => Prp.not A

@[grind]
def size : Prp Atom → ℕ
  | atom _ => 1
  | or A B => A.size + B.size + 1
  | not A => A.size + 1

def and (A B : Prp Atom) : Prp Atom := ¬ (¬ A ∨ ¬ B)

infixl:30 " ∧ " => Prp.and

lemma and_def {A B : Prp Atom} : (A ∧ B) = ¬ (¬ A ∨ ¬ B) := rfl

def verum [Inhabited Atom] : Prp Atom := ¬ default ∨ default

instance [Inhabited Atom] : Top (Prp Atom) where
  top := verum

def falsum [Inhabited Atom] : Prp Atom := ¬ ⊤

instance [Inhabited Atom] : Bot (Prp Atom) where
  bot := falsum

def atomic : Prp Atom → Bool
  | atom _ => true
  | _ => false

lemma atomic_atom (x : Atom) : (Prp.atom x).atomic = true := rfl

def IsPresent (A : Prp Atom) (x : Atom) : Prop :=
  match A with
  | atom y => x = y
  | or A B => A.IsPresent x ∨ B.IsPresent x
  | not A => A.IsPresent x

def atoms : Prp Atom → List Atom
  | atom x => [x]
  | or A B => A.atoms ++ B.atoms
  | not A => A.atoms

theorem mem_atoms_iff {A : Prp Atom} {x : Atom} : x ∈ A.atoms ↔ A.IsPresent x := by
  induction A
  all_goals grind [atoms, IsPresent]

instance [DecidableEq Atom] (A : Prp Atom) (x : Atom) : Decidable (A.IsPresent x) :=
  decidable_of_iff (x ∈ A.atoms) mem_atoms_iff

lemma finite_setOf_isPresent {A : Prp Atom} : Set.Finite {x | A.IsPresent x} := by
  convert ← A.atoms.finite_toSet
  exact mem_atoms_iff

def bigOr [Inhabited Atom] (As : List (Prp Atom)) : Prp Atom := As.foldr (· ∨ ·) ⊥

def bigAnd [Inhabited Atom] (As : List (Prp Atom)) : Prp Atom := ¬ (bigOr <| (As.map (¬ ·)))

end Prp

open Prp

abbrev Conc (Atom : Type u) : Type u := List (Prp Atom)

def Conc.size (Γ : Conc Atom) : ℕ := (Γ.map Prp.size).sum

@[grind =]
lemma Conc.size_cons (A : Prp Atom) (Γ : Conc Atom) : Conc.size (A :: Γ) = A.size + Γ.size := rfl

lemma Conc.size_perm {Γ Γ' : Conc Atom} (h : Γ ~ Γ') : Γ.size = Γ'.size :=
  (h.map Prp.size).sum_nat

def Conc.atomic (Γ : Conc Atom) : Bool := Γ.all Prp.atomic

lemma exists_atom_eq {Γ : Conc Atom} {A : Prp Atom} (hA : A ∈ Γ) (hΓ : Γ.atomic) :
    ∃ x, .atom x = A := by
  cases A with
  | atom x => use x
  | or | not =>
    rw [Conc.atomic, List.all_eq_true] at hΓ
    specialize hΓ _ hA
    simp [Prp.atomic] at hΓ

def cases_atomic_false (Γ : Conc Atom) (hΓ : Γ.atomic = false) :
    {p : Conc Atom × Prp Atom × Prp Atom // ((p.2.1 ∨ p.2.2) :: p.1).Perm Γ} ⊕
      {p : Conc Atom × Prp Atom // ((¬ p.2) :: p.1).Perm Γ} :=
  match Γ with
  | [] => False.elim (by simp [Conc.atomic] at hΓ)
  | Prp.atom x :: Γ =>
    have : Conc.atomic Γ = false := by
      rwa [Conc.atomic, List.all_cons, Prp.atomic_atom, Bool.true_and] at hΓ
    match cases_atomic_false Γ this with
    | Sum.inl ⟨⟨Γ', A, B⟩, h⟩ => Sum.inl ⟨⟨atom x :: Γ', A, B⟩,
      Perm.swap (atom x) (A ∨ B) Γ' |>.trans (h.cons _)⟩
    | Sum.inr ⟨⟨Γ', A⟩, h⟩ => Sum.inr ⟨⟨atom x :: Γ', A⟩,
      Perm.swap (atom x) (¬ A) Γ' |>.trans (h.cons _)⟩
  | Prp.or A B :: Γ => Sum.inl ⟨⟨Γ, A, B⟩, .refl _⟩
  | Prp.not A :: Γ => Sum.inr ⟨⟨Γ, A⟩, .refl _⟩

def atomic_cases (Γ : Conc Atom) :
    Γ.atomic = true ⊕'
      {p : Conc Atom × Prp Atom × Prp Atom // ((p.2.1 ∨ p.2.2) :: p.1).Perm Γ} ⊕
      {p : Conc Atom × Prp Atom // ((¬ p.2) :: p.1).Perm Γ} :=
  match hΓ : Γ.atomic with
  | true => PSum.inl rfl
  | false => PSum.inr (cases_atomic_false Γ hΓ)

def findCommon [DecidableEq Atom] (Γ Δ : Conc Atom) :
    {A : Prp Atom // A ∈ Γ ∧ A ∈ Δ} ⊕' ∀ A ∈ Γ, ∀ B ∈ Δ, A ≠ B :=
  match h : (Γ ∩ Δ).head? with
  | none => PSum.inr <| by
    rw [head?_eq_none_iff, inter_eq_nil_iff_disjoint] at h
    exact List.disjoint_iff_ne.mp h
  | some A => PSum.inl ⟨A, mem_inter_iff.mp <| mem_of_head? h⟩

end CPL
