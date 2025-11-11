import KFOL.Core.Assignment

namespace KFOL

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- Placeholder for building the semantic environment from a completed assignment.
This will be populated when terminals depend on the prefix (Refactor 7.1). -/
def extractEnvStub
    (G : Game K L)
    (a : Assignment (G := G) (𝓜 := 𝓜) G.binders.length) : Unit :=
  ()

end KFOL
