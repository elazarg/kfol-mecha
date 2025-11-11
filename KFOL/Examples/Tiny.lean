import KFOL.Core.Eval

namespace KFOL.Examples

open KFOL
open Classical

instance : (FirstOrder.Language.empty).Structure Unit := ⟨⟩

/-- A minimal two-player game with an empty prefix and constant terminals. -/
noncomputable def trivialGame : Game 2 FirstOrder.Language.empty :=
{ binders := [],
  terminal := fun
  | ⟨0, _⟩ => FirstOrder.Language.BoundedFormula.true
  | ⟨1, _⟩ => FirstOrder.Language.BoundedFormula.false }

/-- Strategies are irrelevant for the empty prefix; this canonical profile suffices. -/
noncomputable def trivialProfile :
    Profile (G := trivialGame) (𝓜 := Unit) :=
  fun _ k _ _ => (False.elim (Nat.not_lt_zero _ k.2))

lemma trivialGame_eval :
    eval (G := trivialGame) (𝓜 := Unit) trivialProfile ⟨0, by decide⟩ = true := by
  have : holds (G := trivialGame) (𝓜 := Unit) ⟨0, by decide⟩ := by
    simp [holds, trivialGame]
  simpa [holds] using
    (eval_true_iff (G := trivialGame) (𝓜 := Unit) trivialProfile ⟨0, by decide⟩).mpr this

#eval eval (G := trivialGame) (𝓜 := Unit) trivialProfile ⟨1, by decide⟩

end KFOL.Examples
