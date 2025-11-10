import KFOL.Core.Strategy

namespace KFOL

open Classical FirstOrder

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- Extend an assignment on the first `k` binders with a value for the `k`-th
binder. -/
def extendAssignment (G : Game K L) (k : ℕ) (hk : k < G.binders.length)
    (a : Assignment (G := G) (𝓜 := 𝓜) k)
    (x : binderCarrier (G := G) (𝓜 := 𝓜) ⟨k, hk⟩) :
    Assignment (G := G) (𝓜 := 𝓜) (k + 1) :=
  fun {j} hj =>
    have hj' : j.1 ≤ k := Nat.lt_succ_iff.mp hj
    if hEq : j.1 = k then
      have hjk : j = ⟨k, hk⟩ := Fin.ext (by simpa using hEq)
      by simpa [hjk] using x
    else
      have hlt : j.1 < k := Nat.lt_of_le_of_ne hj' hEq
      a hlt

/-- Execute a single move in the game using the strategy profile `σ`. -/
def step (G : Game K L) (σ : Profile (G := G) (𝓜 := 𝓜))
    (k : ℕ) (hk : k < G.binders.length)
    (a : Assignment (G := G) (𝓜 := 𝓜) k) :
    Assignment (G := G) (𝓜 := 𝓜) (k + 1) :=
  let kf : MoveIx G := ⟨k, hk⟩
  let r := (G.binders.get kf).role
  let v := obsBroadcast (G := G) (𝓜 := 𝓜) kf a
  let x := σ r kf rfl v
  extendAssignment (G := G) (𝓜 := 𝓜) k hk a x

/-- Evaluate the terminal formulas of a game under a strategy profile. -/
noncomputable def eval (G : Game K L) (_σ : Profile (G := G) (𝓜 := 𝓜)) :
    Role K → Bool :=
  fun i =>
    if _ : FirstOrder.Language.Sentence.Realize (M := 𝓜) (G.terminal i) then
      true
    else
      false

/-- Equality of strategy profiles implies equality of evaluations. -/
@[simp] lemma eval_profile_congr
    (G : Game K L) (σ σ' : Profile (G := G) (𝓜 := 𝓜))
    (_H : ∀ i k h v, σ i k h v = σ' i k h v) :
    eval (G := G) (𝓜 := 𝓜) σ = eval (G := G) (𝓜 := 𝓜) σ' :=
  rfl

end KFOL
