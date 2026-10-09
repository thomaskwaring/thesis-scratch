import Mathlib.Data.Finset.Lattice.Fold
import ThesisScratch.ForCslib.CPL.Defs
import Init.Data.List.Perm
import ThesisScratch.ForMathlib.Data.List

open List Finset

namespace CPL

variable {Atom : Type*}

open Prp

inductive Proof : Conc Atom → Conc Atom → Type _ where
  | ax {A} {Γ Δ} : Proof (A :: Γ) (A :: Δ)
  | cut {A} {Γ Δ} : Proof Γ (A :: Δ) → Proof (A :: Γ) Δ → Proof Γ Δ
  | ex {Γ Γ' Δ Δ'} (hΓ : Γ.Perm Γ') (hΔ : Δ.Perm Δ') : Proof Γ Δ → Proof Γ' Δ'
  | ctrL {A} {Γ Δ} : Proof (A :: A :: Γ) Δ → Proof (A :: Γ) Δ
  | ctrR {A} {Γ Δ} : Proof Γ (A :: A :: Δ) → Proof Γ (A :: Δ)
  | negL {A} {Γ Δ} : Proof Γ (A :: Δ) → Proof ((¬ A) :: Γ) Δ
  | negR {A} {Γ Δ} : Proof (A :: Γ) Δ → Proof Γ ((¬ A) :: Δ)
  | orL {A B} {Γ Δ} : Proof (A :: Γ) Δ → Proof (B :: Γ) Δ → Proof ((A ∨ B) :: Γ) Δ
  | orR {A B} {Γ Δ} : Proof Γ (A :: B :: Δ) → Proof Γ ((A ∨ B) :: Δ)

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

def exL (π : Proof Γ Δ) (h : Γ ~ Γ') : Proof Γ' Δ := π.ex h (.refl _)

def exR (π : Proof Γ Δ) (h : Δ ~ Δ') : Proof Γ Δ' := π.ex (.refl _) h

def swapL (π : Proof (A :: B :: Γ) Δ) : Proof (B :: A :: Γ) Δ := π.exL (.swap ..)

def swapR (π : Proof Γ (A :: B :: Δ)) : Proof Γ (B :: A :: Δ) := π.exR (.swap ..)

def weak {Γ' Δ' : Conc Atom} : {Γ Δ : Conc Atom} → Proof Γ Δ → Proof (Γ ++ Γ') (Δ ++ Δ')
  | _, _, ax => ax
  | _, _, cut π ρ => π.weak.cut ρ.weak
  | _, _, ex h h' π => π.weak.ex (h.append <| .refl Γ') (h'.append <| .refl Δ')
  | _ , _, ctrL π => π.weak.ctrL
  | _, _, ctrR π => π.weak.ctrR
  | _, _, negL π => π.weak.negL
  | _, _, negR π => π.weak.negR
  | _, _, orL π ρ => π.weak.orL ρ.weak
  | _, _, orR π => π.weak.orR

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

def negR' (π : Proof ((¬A) :: Γ) Δ) : Proof Γ (A :: Δ) := axR.cut π.weakConsR

def andL (π : Proof (A :: B :: Γ) Δ) : Proof ((A ∧ B) :: Γ) Δ :=
  π.negR.negR.swapR.orR.negL

def andR (π : Proof Γ (A :: Δ)) (ρ : Proof Γ (B :: Δ)) : Proof Γ ((A ∧ B) :: Δ) :=
  (π.negL.orL ρ.negL).negR

end Combinators

section Eta

def atomicAx : {Γ Δ : Conc Atom} → Proof Γ Δ → Bool
  | (A :: _), _, ax => A.atomic
  | _, _, cut π ρ => π.atomicAx && ρ.atomicAx
  | _, _, ex _ _ π => π.atomicAx
  | _, _, ctrL π => π.atomicAx
  | _, _, ctrR π => π.atomicAx
  | _, _, negL π => π.atomicAx
  | _, _, negR π => π.atomicAx
  | _, _, orL π ρ => π.atomicAx && ρ.atomicAx
  | _, _, orR π => π.atomicAx

def etaAx : {Γ Δ : Conc Atom} → (A : Prp Atom) → Proof (A :: Γ) (A :: Δ)
  | _, _, .atom _ => ax
  | _, _, .or A B => ((etaAx A).orL (etaAx B).swapR).orR
  | _, _, .not A => (etaAx A).negL.swapL.negR

lemma atomicAx_etaAx (A : Prp Atom) : (etaAx A (Γ := Γ) (Δ := Δ)).atomicAx = true := by
  induction A generalizing Γ Δ with
  | atom => rfl
  | or _ _ aih bih => exact Bool.and_eq_true_iff.mpr ⟨aih, bih⟩
  | not _ ih => exact ih

def etaExp : {Γ Δ : Conc Atom} → Proof Γ Δ → Proof Γ Δ
  | (A :: _), _, ax => etaAx A
  | _, _, cut π ρ => π.etaExp.cut ρ.etaExp
  | _, _, ex hΓ hΔ π => π.etaExp.ex hΓ hΔ
  | _, _, ctrL π => π.etaExp.ctrL
  | _, _, ctrR π => π.etaExp.ctrR
  | _, _, negL π => π.etaExp.negL
  | _, _, negR π => π.etaExp.negR
  | _, _, orL π ρ => π.etaExp.orL ρ.etaExp
  | _, _, orR π => π.etaExp.orR

theorem atomicAx_etaExp (π : Proof Γ Δ) : π.etaExp.atomicAx = true := by
  induction π
  all_goals grind [atomicAx_etaAx, etaExp, atomicAx]

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
  | _, _, orL π ρ => π.cutFree && ρ.cutFree
  | _, _, orR π => π.cutFree

def_wanted cutExternal :
    {Γ Δ : Conc Atom} → {A : Prp Atom} → Proof Γ (A :: Δ) →  Proof (A :: Γ) Δ → Proof Γ Δ

theorem_wanted cutExternal_correct {π : Proof Γ (A :: Δ)} {π' : Proof (A :: Γ) Δ}
    (h : π.cutFree = true) (h' : π'.cutFree = true) : (❰cutExternal❱ π π').cutFree = true

end CutElim

end Proof

section Semantics

def Prp.interp {α : Type*} [Max α] [Compl α] (v : Atom → α) : Prp Atom → α
  | atom x => v x
  | or A B => A.interp v ⊔ B.interp v
  | not A => (A.interp v)ᶜ

theorem Proof.sound [DecidableEq Atom] {α : Type*} [BooleanAlgebra α] (v : Atom → α)
    (π : Proof Γ Δ) : Γ.toFinset.inf (Prp.interp v) ≤ Δ.toFinset.sup (Prp.interp v) := by
  induction π with
  | ax => simp
  | cut _ _ ih ih' =>
    rw [toFinset_cons, inf_insert, inf_comm, ← isCompl_compl.le_sup_right_iff_inf_left_le,
      sup_comm] at ih'
    simpa [← sup_inf_right] using le_inf ih ih'
  | ex hΓ hΔ => simpa [toFinset_eq_of_perm _ _ hΓ.symm, toFinset_eq_of_perm _ _ hΔ.symm]
  | ctrL _ ih => simpa using ih
  | ctrR _ ih => simpa using ih
  | negL _ ih =>
    rw [toFinset_cons, sup_insert] at ih
    rwa [toFinset_cons, inf_insert, Prp.interp, inf_comm,
      ← isCompl_compl.le_sup_right_iff_inf_left_le, compl_compl, sup_comm]
  | negR _ ih =>
    rw [toFinset_cons, inf_insert, inf_comm, ← isCompl_compl.le_sup_right_iff_inf_left_le] at ih
    rwa [toFinset_cons, sup_insert, Prp.interp, sup_comm]
  | orL _ _ aih bih => simpa [Prp.interp, inf_sup_right] using sup_le aih bih
  | orR _ ih => simpa [Prp.interp, sup_assoc] using ih

theorem consistency (π : @Proof Atom [] []) : False := by
  classical
  simpa using π.sound (fun _ ↦ True)

def_wanted complete {A : Prp Atom} (h : ∀ (v : Atom → Bool), A.interp v = true) : Proof [] [A]

def Prp.flipFor (A : Prp Atom) (v : Atom → Bool) : Prp Atom :=
    if A.interp v then A else ¬ A

def flipForOfAtoms [DecidableEq Atom] {A : Prp Atom} (v : Atom → Bool) {xs : List Atom}
    (h : ∀ x, A.IsPresent x → x ∈ xs) : Proof (xs.map fun x ↦ (atom x).flipFor v) [A.flipFor v] :=
  match A with
  | atom x =>
    Proof.axMem (A := (atom x).flipFor v)
      (List.mem_map_of_mem (h _ rfl)) (List.mem_singleton_self _)
  | .or A B =>
    match hA : A.interp v with
    | false =>
      match hB : B.interp v with
      | false =>
        let π : Proof _ [¬ A] :=
          flipForOfAtoms (A := A) (xs := xs) v (by grind [Prp.IsPresent]) |>.copy
            rfl (by simp [flipFor, hA])
        let ρ : Proof _ [¬ B] :=
          flipForOfAtoms (A := B) (xs := xs) v (by grind [Prp.IsPresent]) |>.copy
            rfl (by simp [flipFor, hB])
        (π.negL'.orL ρ.negL').negR.copy rfl <| by simp [flipFor, interp, hA, hB]
      | true =>
        let π := flipForOfAtoms (A := B) (xs := xs) v (by grind [Prp.IsPresent])
        (π.weakConsR (A := A)).orR.copy rfl <| by simp [flipFor, hB, interp]
    | true =>
      let π := flipForOfAtoms (A := A) (xs := xs) v (by grind [Prp.IsPresent])
      (π.weakR (Δ' := [B])).orR.copy rfl <| by simp [flipFor, hA, interp]
  | .not A =>
    match hA : A.interp v with
    | true => flipForOfAtoms (A := A) (xs := xs) v (by grind [Prp.IsPresent]) |>.negL.negR.copy
      rfl (by simp [interp, flipFor, hA])
    | false => flipForOfAtoms (A := A) (xs := xs) v (by grind [Prp.IsPresent]) |>.copy
      rfl (by simp [interp, flipFor, hA])

def flipForAtomsTail [DecidableEq Atom] (A : Prp Atom) (x : Atom) (xs : List Atom) (h : x ∉ xs)
    (πs : ∀ (v : Atom → Bool), Proof ((x :: xs).map fun x ↦ (atom x).flipFor v) [A])
    (v : Atom → Bool) : Proof (xs.map fun x ↦ (atom x).flipFor v) [A] :=
  let π₁ : Proof (atom x :: xs.map fun x ↦ (atom x).flipFor v) [A] :=
    πs (Function.update v x true) |>.copy (by simp [flipFor, interp]; grind) rfl
  let π₂ : Proof ((¬ atom x) :: xs.map fun x ↦ (atom x).flipFor v) [A] :=
    πs (Function.update v x false) |>.copy (by simp [flipFor, interp]; grind) rfl
  π₁.cutL π₂

def nilOfFlipForAtoms [DecidableEq Atom] (A : Prp Atom) : (xs : List Atom) → xs.Nodup →
    (∀ (v : Atom → Bool), Proof (xs.map fun x ↦ (atom x).flipFor v) [A]) → Proof [] [A]
  | [], _, h => h default
  | x :: xs, h, πs => nilOfFlipForAtoms A xs h.tail (flipForAtomsTail A x xs h.notMem πs)

def ofForallInterpTrue [DecidableEq Atom] (A : Prp Atom)
    (hA : ∀ (v : Atom → Bool), A.interp v = true) : Proof [] [A] :=
  nilOfFlipForAtoms A A.atoms.dedup A.atoms.nodup_dedup fun v ↦
    flipForOfAtoms (A := A) (xs := A.atoms.dedup) v (by simp [mem_atoms_iff]) |>.copy
      rfl (by simp [flipFor, hA v])

def axOrCountermodel [DecidableEq Atom] {Γ Δ : Conc Atom} (hΓ : Γ.atomic) (hΔ : Δ.atomic) :
    {π : Proof Γ Δ // π.cutFree = true} ⊕
    {v : Atom → Bool // (∀ A ∈ Γ, A.interp v = true) ∧ (∀ B ∈ Δ, B.interp v = false)} :=
  match findCommon Γ Δ with
  | PSum.inl ⟨A, hAΓ, hAΔ⟩ => Sum.inl ⟨Proof.axMem hAΓ hAΔ, rfl⟩
  | PSum.inr h => Sum.inr ⟨fun x => if atom x ∈ Γ then true else false, by
    intro A hA
    obtain ⟨x, rfl⟩ : ∃ x, atom x = A := exists_atom_eq hA hΓ
    simp [interp, hA], by
    intro B hB
    obtain ⟨x, rfl⟩ : ∃ x, atom x = B := exists_atom_eq hB hΔ
    have : ¬ atom x ∈ Γ := fun hB' ↦ h _ hB' _ hB rfl
    simp [interp, this]
  ⟩

def proofOrCountermodel [DecidableEq Atom] (Γ Δ : Conc Atom) : {π : Proof Γ Δ // π.cutFree = true} ⊕
    {v : Atom → Bool // (∀ A ∈ Γ, A.interp v = true) ∧ (∀ B ∈ Δ, B.interp v = false)} :=
  match atomic_cases Γ with
  | .inl hΓ =>
    match atomic_cases Δ with
    | .inl hΔ => axOrCountermodel hΓ hΔ
    | .inr (.inl ⟨⟨Δ', A, B⟩, (h : (A ∨ B) :: Δ' ~ Δ)⟩) =>
      have : Conc.size (A :: B :: Δ') < Δ.size := by grind [Conc.size_perm h.symm]
      match proofOrCountermodel Γ (A :: B :: Δ') with
      | .inl ⟨π, hπ⟩ => .inl ⟨π.orR.exR h, hπ⟩
      | .inr ⟨v, hΓ, hΔ⟩ => .inr ⟨v, hΓ, by
          simp_rw [← h.mem_iff, List.mem_cons]
          rintro B (rfl | hB)
          · simp [interp, hΔ A mem_cons_self, hΔ B (by grind)]
          · exact hΔ B (by grind)
        ⟩
    | .inr (.inr ⟨⟨Δ', A⟩, (h : (¬ A) :: Δ' ~ Δ)⟩) =>
      have : Conc.size (A :: Γ) + Δ'.size < Γ.size + Δ.size := by grind [Conc.size_perm h.symm]
      match proofOrCountermodel (A :: Γ) Δ' with
      | .inl ⟨π, hπ⟩ => .inl ⟨π.negR.exR h, hπ⟩
      | .inr ⟨v, hΓ, hΔ⟩ => .inr ⟨v, fun A' hA' ↦ hΓ A' (List.mem_cons_of_mem A hA') , by
          simp_rw [← h.mem_iff, List.mem_cons]
          rintro B (rfl | hB)
          · simp [interp, hΓ A mem_cons_self]
          · exact hΔ B hB
        ⟩
  | .inr (.inl ⟨⟨Γ', A, B⟩, (h : (A ∨ B) :: Γ' ~ Γ)⟩) =>
    have : Conc.size (A :: Γ') < Γ.size := by grind [Conc.size_perm h.symm]
    have : Conc.size (B :: Γ') < Γ.size := by grind [Conc.size_perm h.symm]
    match proofOrCountermodel (A :: Γ') Δ with
    | .inl ⟨π, hπ⟩ =>
      match proofOrCountermodel (B :: Γ') Δ with
      | .inl ⟨ρ, hρ⟩ => .inl ⟨(π.orL ρ).exL h, by simp [Proof.cutFree, Proof.exL, hπ, hρ]⟩
      | .inr ⟨v, hΓ, hΔ⟩ => .inr ⟨v, by {
        simp_rw [← h.mem_iff, List.mem_cons]
        rintro A (rfl | hA)
        · simp [interp, hΓ B mem_cons_self]
        · exact hΓ A (List.mem_cons_of_mem _ hA)
      }, hΔ⟩
    | .inr ⟨v, hΓ, hΔ⟩ => .inr ⟨v, by {
      simp_rw [← h.mem_iff, List.mem_cons]
      rintro A (rfl | hA)
      · simp [interp, hΓ A mem_cons_self]
      · exact hΓ A (List.mem_cons_of_mem _ hA)
      }, hΔ⟩
  | .inr (.inr ⟨⟨Γ', A⟩, (h : (¬ A) :: Γ' ~ Γ)⟩) =>
    have : Γ'.size + Conc.size (A :: Δ) < Γ.size + Δ.size := by grind [Conc.size_perm h.symm]
    match proofOrCountermodel Γ' (A :: Δ) with
    | .inl ⟨π, hπ⟩ => .inl ⟨π.negL.exL h, hπ⟩
    | .inr ⟨v, hΓ, hΔ⟩ => .inr ⟨v, by {
        simp_rw [← h.mem_iff, List.mem_cons]
        rintro A (rfl | hA)
        · simp [interp, hΔ A mem_cons_self]
        · exact hΓ A hA
      }, fun B hB ↦ hΔ B (mem_cons_of_mem A hB)⟩
  termination_by Γ.size + Δ.size

def cutElim [DecidableEq Atom] {Γ Δ : Conc Atom} (π : Proof Γ Δ) :
    {π' : Proof Γ Δ // π'.cutFree = true} :=
  match proofOrCountermodel Γ Δ with
  | .inl π' => π'
  | .inr ⟨v, hΓ, hΔ⟩ => False.elim <| by
    apply Bool.false_lt_true.not_ge
    convert π.sound v
    · rw [← top_eq_true, Eq.comm, Finset.inf_eq_top_iff]
      simpa
    · rw [← bot_eq_false, Eq.comm, Finset.sup_eq_bot_iff]
      simpa

end Semantics

end CPL
