import KFOL.Core.Eval

namespace KFOL

open Classical

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- The strategies of all players other than `i`. -/
def Opponents (G : Game K L) (i : Role K) : Type _ :=
  ∀ j, j ≠ i → Strategy (G := G) (𝓜 := 𝓜) j

/-- Combine a strategy for role `i` with strategies for the other players. -/
def merge (G : Game K L) (i : Role K)
    (σi : Strategy (G := G) (𝓜 := 𝓜) i)
    (opp : Opponents (G := G) (𝓜 := 𝓜) i) :
    Profile (G := G) (𝓜 := 𝓜) :=
  fun j =>
    if h : j = i then by cases h; exact σi
    else opp j h

/-- Player `i` can force her objective if she has a strategy that succeeds
against every profile of the other players. -/
def Forceable (G : Game K L) (i : Role K) : Prop :=
  ∃ σi : Strategy (G := G) (𝓜 := 𝓜) i,
    ∀ opp : Opponents (G := G) (𝓜 := 𝓜) i,
      eval (G := G) (𝓜 := 𝓜) (merge (G := G) (𝓜 := 𝓜) i σi opp) i = true

end KFOL
