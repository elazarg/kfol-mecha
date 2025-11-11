import KFOL.Core.BinderGame

namespace KFOL

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u}

/-- The carrier type associated with the `j`-th binder of a game under the
structure `𝓜`. -/
def binderCarrier (G : Game K L) [L.Structure 𝓜]
    (j : MoveIx G) : Type u := 𝓜

/-- Assignments store the values chosen for the first `k` binders of the game. -/
def Assignment (G : Game K L) [L.Structure 𝓜] (k : ℕ) : Type u :=
  ∀ {j : MoveIx G}, j.1 < k → binderCarrier (G := G) (𝓜 := 𝓜) j

@[simp] lemma binderCarrier_single_sorted (G : Game K L) [L.Structure 𝓜]
    (j : MoveIx G) : binderCarrier (G := G) (𝓜 := 𝓜) j = 𝓜 := rfl

@[simp] lemma binderCarrier_mk (G : Game K L) [L.Structure 𝓜]
    {k : ℕ} (hk : k < G.binders.length) :
    binderCarrier (G := G) (𝓜 := 𝓜) ⟨k, hk⟩ = 𝓜 := rfl

end KFOL
