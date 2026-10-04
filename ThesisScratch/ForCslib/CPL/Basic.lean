import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common
import Init.Data.List.Perm

open List Finset

namespace CPL

inductive Prp (Atom : Type u) : Type u where
  | atom (x : Atom) : Prp Atom
  | and (A B : Prp Atom) : Prp Atom
  | not (A : Prp Atom) : Prp Atom
  deriving DecidableEq

variable {Atom : Type*}

namespace Prp

infixl:35 " ∧ " => Prp.and
notation:max "¬" A:45 => Prp.not A

def or (A B : Prp Atom) : Prp Atom := ¬ (¬ A ∧ ¬ B)

infixl:30 " ∨ " => Prp.or

lemma or_def {A B : Prp Atom} : (A ∨ B) = ¬ (¬ A ∧ ¬ B) := rfl

def atomic : Prp Atom → Bool
  | atom _ => true
  | _ => false

end Prp

abbrev Conc (Atom : Type u) : Type u := List (Prp Atom)

inductive Proof : Conc Atom → Conc Atom → Type _ where
  | ax {A} {Γ Δ} : Proof (A :: Γ) (A :: Δ)
  | cut {A} {Γ Δ} : Proof Γ (A :: Δ) → Proof (A :: Γ) Δ → Proof Γ Δ
  | ex {Γ Γ' Δ Δ'} (hΓ : Γ.Perm Γ') (hΔ : Δ.Perm Δ') : Proof Γ Δ → Proof Γ' Δ'
  | ctrL {A} {Γ Δ} : Proof (A :: A :: Γ) Δ → Proof (A :: Γ) Δ
  | ctrR {A} {Γ Δ} : Proof Γ (A :: A :: Δ) → Proof Γ (A :: Δ)
  | negL {A} {Γ Δ} : Proof Γ (A :: Δ) → Proof ((¬ A) :: Γ) Δ
  | negR {A} {Γ Δ} : Proof (A :: Γ) Δ → Proof Γ ((¬ A) :: Δ)
  | andL {A B} {Γ Δ} : Proof (A :: B :: Γ) Δ → Proof ((A ∧ B) :: Γ) Δ
  | andR {A B} {Γ Δ} : Proof Γ (A :: Δ) → Proof Γ (B :: Δ) → Proof Γ ((A ∧ B) :: Δ)

variable {A B : Prp Atom} {Γ Γ' Δ Δ' : Conc Atom}

namespace Proof

section Combinators

def copy (hΓ : Γ = Γ') (hΔ : Δ = Δ') (π : Proof Γ Δ) : Proof Γ' Δ' := hΓ ▸ hΔ ▸ π

def axMem [DecidableEq Atom] (h : A ∈ Γ) (h' : A ∈ Δ) : Proof Γ Δ :=
  ex (perm_cons_erase h).symm (perm_cons_erase h').symm ax

def axL : Proof ((¬A) :: A :: Γ) Δ := ax.negL

def axR : Proof Γ ((¬A) :: A :: Δ) := ax.negR

def cutL (π : Proof (A :: Γ) Δ) (ρ : Proof ((¬A) :: Γ) Δ) : Proof Γ Δ := π.negR.cut ρ

def cutR (π : Proof Γ (A :: Δ)) (ρ : Proof Γ ((¬A) :: Δ)) : Proof Γ Δ := ρ.cut π.negL

def swapL (π : Proof (A :: B :: Γ) Δ) : Proof (B :: A :: Γ) Δ := π.ex (.swap ..) (.refl _)

def swapR (π : Proof Γ (A :: B :: Δ)) : Proof Γ (B :: A :: Δ) := π.ex (.refl _) (.swap ..)

def weak {Γ' Δ' : Conc Atom} : {Γ Δ : Conc Atom} → Proof Γ Δ → Proof (Γ ++ Γ') (Δ ++ Δ')
  | _, _, ax => ax
  | _, _, cut π ρ => π.weak.cut ρ.weak
  | _, _, ex h h' π => π.weak.ex (h.append <| .refl Γ') (h'.append <| .refl Δ')
  | _ , _, ctrL π => π.weak.ctrL
  | _, _, ctrR π => π.weak.ctrR
  | _, _, negL π => π.weak.negL
  | _, _, negR π => π.weak.negR
  | _, _, andL π => π.weak.andL
  | _, _, andR π ρ => π.weak.andR ρ.weak

def weakL (π : Proof Γ Δ) : Proof (Γ ++ Γ') Δ := π.weak.copy rfl (append_nil Δ)

def weakR (π : Proof Γ Δ) : Proof Γ (Δ ++ Δ') := π.weak.copy (append_nil Γ) rfl

def weakPre (π : Proof Γ Δ) : Proof (Γ' ++ Γ) (Δ' ++ Δ) :=
    π.weak.ex perm_append_comm perm_append_comm

def weakPreL (π : Proof Γ Δ) : Proof (Γ' ++ Γ) Δ := π.weakPre.copy rfl (nil_append Δ)

def weakPreR (π : Proof Γ Δ) : Proof Γ (Δ' ++ Δ) := π.weakPre.copy (nil_append Γ) rfl

def weakConsL (π : Proof Γ Δ) : Proof (A :: Γ) Δ := π.weakPreL (Γ' := [A])

def weakConsR (π : Proof Γ Δ) : Proof Γ (A :: Δ) := π.weakPreR (Δ' := [A])

def dneL : Proof ((¬¬A) :: Γ) (A :: Δ) := ax.negR.negL

def dneR : Proof (A :: Γ) ((¬¬A) :: Δ) := ax.negL.negR

def negL' (π : Proof Γ ((¬A) :: Δ)) : Proof (A :: Γ) Δ := π.weakConsL.cut axL

def negR' (π : Proof ((¬ A) :: Γ) Δ) : Proof Γ (A :: Δ) := axR.cut π.weakConsR

def orL (πA : Proof (A :: Γ) Δ) (πB : Proof (B :: Γ) Δ) : Proof ((A ∨ B) :: Γ) Δ :=
  (πA.negR.andR πB.negR).negL

def orR (π : Proof Γ (A :: B :: Δ)) : Proof Γ ((A ∨ B) :: Δ) :=
  π.negL.negL.swapL.andL.weakConsR.cutL ax

-- def ctrL (π : Proof (A :: A :: Γ) Δ) : Proof (A :: Γ) Δ := (ax.andR ax).cut π.weakConsL.andL

-- def ctrL' [DecidableEq Atom] : {Γ Δ : Conc Atom} → Proof Γ Δ → Proof Γ.dedup Δ.dedup

--   -- | Γ, (_ :: Δ), ax => ax
--   -- | Γ, Δ, ex h h' π => by

-- -- def ctrR (π : Proof Γ (A :: A :: Δ)) : Proof Γ (A :: Δ) := π.cut ax

end Combinators

section Eta

-- def atomicAx : {Γ Δ : Conc Atom} → Proof Γ Δ → Bool
--   | (A :: _), _, ax => A.atomic
--   | _, _, cut π ρ => π.atomicAx && ρ.atomicAx
--   | _, _, ex _ _ π => π.atomicAx
--   | _, _, ctrL π => π.atomicAx
--   | _, _, ctrR π => π.atomicAx
--   | _, _, negL π => π.atomicAx
--   | _, _, negR π => π.atomicAx
--   | _, _, andL π => π.atomicAx
--   | _, _, andR π ρ => π.atomicAx && ρ.atomicAx


-- def etaAx : {Γ Δ : Conc Atom} → (A : Prp Atom) → Proof (A :: Γ) (A :: Δ)
--   | _, _, .atom _ => ax
--   | _, _, .and A B => ((etaAx A).andR (etaAx B).swapL).andL
--   | _, _, .not A => (etaAx A).negL.swapL.negR

-- lemma atomicAx_etaAx (A : Prp Atom) : (etaAx A (Γ := Γ) (Δ := Δ)).atomicAx = true := by
--   induction A generalizing Γ Δ with
--   | atom => rfl
--   | and _ _ aih bih => exact Bool.and_eq_true_iff.mpr ⟨aih, bih⟩
--   | not _ ih => exact ih

-- def etaExp : {Γ Δ : Conc Atom} → Proof Γ Δ → Proof Γ Δ
--   | (A :: _), _, ax => etaAx A
--   | _, _, cut π ρ => π.etaExp.cut ρ.etaExp
--   | _, _, ex hΓ hΔ π => π.etaExp.ex hΓ hΔ
--   | _, _, ctrL π => π.etaExp.ctrL
--   | _, _, ctrR π => π.etaExp.ctrR
--   | _, _, negL π => π.etaExp.negL
--   | _, _, negR π => π.etaExp.negR
--   | _, _, andL π => π.etaExp.andL
--   | _, _, andR π ρ => π.etaExp.andR ρ.etaExp

-- theorem atomicAx_etaExp (π : Proof Γ Δ) : π.etaExp.atomicAx = true := by
--   induction π
--   case ax => exact atomicAx_etaAx _
--   all_goals simp_all [etaExp, atomicAx]

end Eta

section CutElim

def cutFree : {Γ Δ : Conc Atom} → Proof Γ Δ → Bool
  | _, _, ax => true
  | _, _, cut _ _ => false
  | _, _, ex _ _ π => π.cutFree
  | _, _, ctrL π => π.cutFree
  | _, _, ctrR π => π.cutFree
  | _, _, negL π => π.cutFree
  | _, _, negR π => π.cutFree
  | _, _, andL π => π.cutFree
  | _, _, andR π ρ => π.cutFree && ρ.cutFree

-- set_option match.maxCounterExamples 15
-- def cutExternal :
--     {Γ Δ : Conc Atom} → {A : Prp Atom} → Proof Γ (A :: Δ) →  Proof (A :: Γ) Δ → Proof Γ Δ
--   | _, _, _, ax, π => π.ctrL
--   | Γ, Δ, A, cut π π', ρ => by
  -- | _, _, _, π, ax => π.ctrR
  -- | (_ :: Γ), Δ, A, ax, ex h h' π => (π.ex h h').ctrL

-- theorem_wanted cutExternal_correct {π : Proof Γ (A :: Δ)} {π' : Proof (A :: Γ) Δ}
--     (h : π.cutFree = true) (h' : π'.cutFree = true) : (❰cutExternal❱ π π').cutFree = true

end CutElim

end Proof

-- section Semantics

-- def Prp.interp {α : Type*} [Min α] [Compl α] (v : Atom → α) : Prp Atom → α
--   | atom x => v x
--   | and A B => A.interp v ⊓ B.interp v
--   | not A => (A.interp v)ᶜ

-- theorem Proof.sound [DecidableEq Atom] {α : Type*} [BooleanAlgebra α] (v : Atom → α)
--     (π : Proof Γ Δ) : Γ.toFinset.inf (Prp.interp v) ≤ Δ.toFinset.sup (Prp.interp v) := by
--   induction π with
--   | ax => simp
--   | ex hΓ hΔ => simpa [toFinset_eq_of_perm _ _ hΓ.symm, toFinset_eq_of_perm _ _ hΔ.symm]
--   | negL _ ih =>
--     rw [toFinset_cons, sup_insert] at ih
--     rwa [toFinset_cons, inf_insert, Prp.interp, inf_comm,
--       ← isCompl_compl.le_sup_right_iff_inf_left_le, compl_compl, sup_comm]
--   | negR _ ih =>
--     rw [toFinset_cons, inf_insert, inf_comm, ← isCompl_compl.le_sup_right_iff_inf_left_le] at ih
--     rwa [toFinset_cons, sup_insert, Prp.interp, sup_comm]
--   | andL _ ih => simpa [Prp.interp, inf_assoc] using ih
--   | andR _ _ aih bih => simpa [Prp.interp, sup_inf_right] using le_inf aih bih
--   | cut _ _ ih ih' =>
--     rw [toFinset_cons, inf_insert, inf_comm, ← isCompl_compl.le_sup_right_iff_inf_left_le,
--       sup_comm] at ih'
--     simpa [← sup_inf_right] using le_inf ih ih'

-- theorem consistency (π : @Proof Atom [] []) : False := by
--   classical
--   simpa using π.sound (fun _ ↦ True)

-- end Semantics

end CPL
