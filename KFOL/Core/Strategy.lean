import KFOL.Core.Observation

namespace KFOL

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- Pure strategies for a role select a value for each of their binders based on
its visible history. -/
def Strategy (G : Game K L) (i : Role K) : Type _ :=
  ∀ (k : MoveIx G), (G.binders.get k).role = i →
    View (G := G) (𝓜 := 𝓜) → binderCarrier (G := G) (𝓜 := 𝓜) k

/-- A strategy profile collects a strategy for every role. -/
abbrev Profile (G : Game K L) := ∀ i, Strategy (G := G) (𝓜 := 𝓜) i

end KFOL
