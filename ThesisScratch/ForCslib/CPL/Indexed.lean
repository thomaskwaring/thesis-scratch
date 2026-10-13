import ThesisScratch.ForCslib.CPL.Defs
import Mathlib.Data.Finset.Lattice.Fold

namespace CPL

universe u v

open Set Finset

variable {Atom : Type u}

open Prp

inductive IProof : {α β : Type v} → (α → Prp Atom) → (β → Prp Atom) → Type _ where
  | ax (A : Prp Atom) : @IProof PUnit PUnit (fun _ ↦ A) (fun _ ↦ A)
  | str {l : α → Prp Atom} {l' : α' → Prp Atom} {r : β → Prp Atom} {r' : β' → Prp Atom}
      {el : α → α'} {er : β → β'} (hl : l' ∘ el = l) (hr : r' ∘ er = r) :
      IProof l r → IProof l' r'
  | negL {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom} :
      IProof l (Option.rec A r) → IProof (Option.rec (¬ A) l) r
  | negR {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom} :
      IProof (Option.rec A l) r → IProof l (Option.rec (¬ A) r)
  | orL {l : α → Prp Atom} {r : β → Prp Atom} {A B : Prp Atom} :
      IProof (Option.rec A l) r → IProof (Option.rec B l) r → IProof (Option.rec (A ∧ B) l) r
  | orR {l : α → Prp Atom} {r : β → Prp Atom} {A B : Prp Atom} :
      IProof l (Option.rec A <| Option.rec B r) → IProof l (Option.rec (A ∧ B) r)

namespace IProof

def_wanted cut {l : α → Prp Atom} {r : β → Prp Atom} {A : Prp Atom}
     (π : IProof l (Option.rec A r)) (ρ : IProof (Option.rec A l) r) : IProof l r



end IProof

end CPL
