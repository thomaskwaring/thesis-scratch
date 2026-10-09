import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Subperm

/-!-/

namespace List

variable {α : Type*} {l l₁ l₂ : List α} {x y : α}

section DecidableEq

variable [DecidableEq α]

lemma notMem_dedup : x ∉ l.dedup ↔ x ∉ l := not_iff_not.mpr mem_dedup

lemma dedup_cons_perm_cons : (x :: l).dedup.Perm (x :: l.dedup.erase x) := by
  by_cases h : x ∈ l
  · rw [dedup_cons_of_mem h]
    exact perm_cons_erase (mem_dedup.mpr h)
  · rw [dedup_cons_of_notMem h, erase_of_not_mem (notMem_dedup.mpr h)]

def pullOcc (l : List α) (x : α) : List α × List α :=
  match l with
  | [] => ([], [])
  | y :: l =>
    let (l₁, l₂) := l.pullOcc x
    if x = y then (x :: l₁, l₂) else (l₁, y :: l₂)

lemma pullOcc_perm (l : List α) (x : α) : l.Perm ((l.pullOcc x).1 ++ (l.pullOcc x).2) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    by_cases h : x = y
    · simpa [pullOcc, h] using ih
    · simpa [pullOcc, h] using perm_cons_append_cons y ih

lemma eq_of_mem_pullOcc_fst (h : y ∈ (l.pullOcc x).1) : y = x := by
  fun_induction List.pullOcc l x
  all_goals grind

lemma ne_of_mem_pullOcc_snd (h : y ∈ (l.pullOcc x).2) : y ≠ x := by
  fun_induction List.pullOcc l x
  all_goals grind

lemma notMem_pullOcc_snd : x ∉ (l.pullOcc x).2 := by grind [ne_of_mem_pullOcc_snd]

lemma pullOcc_fst_eq_replicate_count : (l.pullOcc x).1 = replicate (l.count x) x := by
  rw [eq_replicate_iff]
  refine ⟨?_, fun _ => eq_of_mem_pullOcc_fst⟩
  classical
  rw [(l.pullOcc_perm x).count_eq x, count_append, Eq.comm,
    (l.pullOcc x).2.count_eq_zero.mpr notMem_pullOcc_snd, Nat.add_zero, count_eq_length]
  exact fun _ h => (eq_of_mem_pullOcc_fst h).symm

lemma dedup_cons_perm : (x :: l).dedup ~ x :: l.dedup.erase x := by
  by_cases h : x ∈ l
  · rw [dedup_cons_of_mem h]
    exact perm_cons_erase (mem_dedup.mpr h)
  · simp [dedup_cons_of_notMem h, erase_of_not_mem (notMem_dedup.mpr h)]

end DecidableEq

lemma subperm_iff' : l₁ <+~ l₂ ↔ ∃ l, l ~ l₂ ∧ l₁ <+: l := by
  constructor
  · intro ⟨l, hperm, hsub⟩
    obtain ⟨l', hperm'⟩ := hsub.exists_perm_append
    refine ⟨l₁ ++ l', ?_, l', rfl⟩
    exact (hperm.symm.append_right l').trans hperm'.symm
  · intro ⟨l, hl, hl'⟩
    exact hl'.sublist.subperm.trans hl.subperm


end List
