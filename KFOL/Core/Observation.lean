import Mathlib.Data.List.FinRange
import KFOL.Core.Assignment

namespace KFOL

open scoped List

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- The visible history for the `k`-th move, represented as a list of binder
indices paired with their values. -/
abbrev View (G : Game K L) (k : MoveIx G) : Type _ :=
  List (Σ j : MoveIx G, binderCarrier (G := G) (𝓜 := 𝓜) j)

/-- Broadcast visibility: at step `k`, every earlier move (in syntactic order)
is visible together with its value. -/
def obsBroadcast (G : Game K L) (k : MoveIx G)
    (a : Assignment (G := G) (𝓜 := 𝓜) k.1) :
    View (G := G) (𝓜 := 𝓜) k :=
  (List.finRange k.1).map fun (j : Fin k.1) =>
    let j' : MoveIx G := ⟨j, Nat.lt_trans j.2 k.2⟩
    ⟨j', a (show j'.1 < k.1 from j.2)⟩

end KFOL
