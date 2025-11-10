import KFOL.Core.BinderGame

namespace KFOL

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u}

/-- Indices for binder occurrences in the prefix of a game. -/
abbrev MoveIx (G : Game K L) := Fin G.binders.length

/-- The carrier type associated with the `j`-th binder of a game under the
structure `𝓜`. -/
@[simp] def binderCarrier (G : Game K L) [L.Structure 𝓜]
    (j : MoveIx G) : Type u := 𝓜

/-- Assignments store the values chosen for the first `k` binders of the game. -/
@[simp] def Assignment (G : Game K L) [L.Structure 𝓜] (k : ℕ) : Type u :=
  ∀ {j : MoveIx G}, j.1 < k → binderCarrier (G := G) (𝓜 := 𝓜) j

end KFOL
