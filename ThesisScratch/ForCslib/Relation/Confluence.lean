import Cslib.Foundations.Relation.Confluence

namespace Relation

variable {α : Type*}

def LocallyCommute (r s : α → α → Prop) : Prop :=
  ∀ {x y y' : α}, r x y → s x y' → ∃ z, ReflTransGen s y z ∧ ReflTransGen r y' z

theorem newmann {r s : α → α → Prop} (h : LocallyCommute r s) (h' : Terminating (r ⊔ s)) :
    Commute r s := by
  intro x
  induction x using h'.induction with | h x ih =>
  intro y z xy xz
  rcases xy.cases_head with (rfl | ⟨y₁, xy₁, y₁y⟩)
  · use z
  · rcases xz.cases_head with (rfl | ⟨z₁, xz₁, z₁z⟩)
    · use y, .refl, xy
    · obtain ⟨u, y₁u, z₁u⟩ := h xy₁ xz₁
      obtain ⟨v, yv, uv⟩ := ih y₁ (Or.inl xy₁) y₁y y₁u
      obtain ⟨w, vw, zw⟩ := ih z₁ (Or.inr xz₁) (z₁u.trans uv) z₁z
      use w, (yv.trans vw), zw

theorem Terminating.sup_of_comp_le {r s : α → α → Prop} (hr : Terminating r) (hs : Terminating s)
    (h : Comp r s ≤ s) : Terminating (r ⊔ s) := by
  rw [Terminating.iff_forall_sn]
  intro x
  induction x using hs.induction with | h x ihs =>
  induction x using hr.induction with | h x ihr =>
  rw [SN_iff_SN_of_rel]
  rintro y (hxy | hxy)
  · refine ihr y hxy ?_
    intro z hyz
    refine ihs z (h x z ?_)
    use y
  · exact ihs y hxy

end Relation
