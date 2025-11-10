import KFOL.Core.Eval

namespace KFOL

open Classical

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u} [L.Structure 𝓜]

/-- Permute the roles in a game. -/
def permRolesGame (π : Equiv.Perm (Role K)) (G : Game K L) : Game K L :=
{ binders := G.binders.map fun b =>
    { role := π b.role, name := b.name, sortName := b.sortName },
  terminal := fun i => G.terminal (π.symm i) }

/-- Transport a strategy profile along a role permutation. -/
def permProfile (π : Equiv.Perm (Role K)) (G : Game K L)
    (σ : Profile (G := G) (𝓜 := 𝓜)) :
    Profile (G := permRolesGame (K := K) (L := L) π G) (𝓜 := 𝓜) :=
  fun i k hk v =>
    have hklen : (permRolesGame π G).binders.length = G.binders.length := by
      simp [permRolesGame]
    let k' : MoveIx G := Fin.cast hklen k
    have hk' : (G.binders.get k').role = π.symm i := by
      have := congrArg (fun r => π.symm r) (by
        simpa [permRolesGame, hklen, k'] using hk)
      simpa using this
    let v' : View (G := G) (𝓜 := 𝓜) k' :=
      v.map fun entry => ⟨Fin.cast hklen entry.1, entry.2⟩
    σ (π.symm i) k' hk' v'

/-- Permute the components of an outcome vector. -/
def permOutcome (π : Equiv.Perm (Role K)) (o : Role K → Bool) : Role K → Bool :=
  fun i => o (π.symm i)

/-- Evaluation is equivariant under the action of the symmetric group. -/
@[simp] theorem equivariant_eval (π : Equiv.Perm (Role K))
    (G : Game K L) (σ : Profile (G := G) (𝓜 := 𝓜)) :
    eval (G := permRolesGame (K := K) (L := L) π G) (𝓜 := 𝓜)
        (permProfile (K := K) (L := L) (𝓜 := 𝓜) π G σ)
      = permOutcome (K := K) π (eval (G := G) (𝓜 := 𝓜) σ) :=
  rfl

end KFOL
