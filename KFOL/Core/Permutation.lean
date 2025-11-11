import KFOL.Core.Eval

namespace KFOL

open Classical

universe u

variable {K : ℕ} {L : FirstOrder.Language}
variable {𝓜 : Type u}

/-- Permute the roles in a game. -/
def permRolesGame (π : Equiv.Perm (Role K)) (G : Game K L) : Game K L :=
{ binders := G.binders.map fun b =>
    { role := π b.role, name := b.name, sortName := b.sortName },
  terminal := fun i => G.terminal (π.symm i) }

@[simp] lemma permRolesGame_binders_length
    (π : Equiv.Perm (Role K)) (G : Game K L) :
    (permRolesGame (K := K) (L := L) π G).binders.length = G.binders.length := by
  simp [permRolesGame]

/-- Casting a binder index along the length equality produced by `permRolesGame`
does not change its underlying natural number. -/
@[simp] lemma permRolesGame_cast_eq
    (π : Equiv.Perm (Role K)) (G : Game K L)
    (k : MoveIx (permRolesGame (K := K) (L := L) π G)) :
    (Fin.cast
        (permRolesGame_binders_length (K := K) (L := L) (π := π) (G := G))
        k).1 = k.1 := rfl

section

variable [L.Structure 𝓜]

/-- Under role permutation, the `holds` predicate is precomposed by `π.symm`. -/
@[simp] lemma holds_perm (π : Equiv.Perm (Role K))
    (G : Game K L) (i : Role K) :
    holds (G := permRolesGame (K := K) (L := L) π G) (𝓜 := 𝓜) i
      = holds (G := G) (𝓜 := 𝓜) (π.symm i) := rfl

/-- Transport a strategy profile along a role permutation. -/
def permProfile (π : Equiv.Perm (Role K)) (G : Game K L)
    (σ : Profile (G := G) (𝓜 := 𝓜)) :
    Profile (G := permRolesGame (K := K) (L := L) π G) (𝓜 := 𝓜) :=
  fun i k hk v =>
    have hklen := permRolesGame_binders_length (K := K) (L := L) (π := π) (G := G)
    let k' : MoveIx G := Fin.cast hklen k
    have hk' : (G.binders.get k').role = π.symm i := by
      have := congrArg (fun r => π.symm r) (by
        simpa [permRolesGame, hklen, k'] using hk)
      simpa using this
    let v' : View (G := G) (𝓜 := 𝓜) k' :=
      v.map fun entry => ⟨Fin.cast hklen entry.1, entry.2⟩
    σ (π.symm i) k' hk' v'

/-- Permute the components of an outcome vector. -/
@[simp] def permOutcome (π : Equiv.Perm (Role K)) (o : Role K → Bool) : Role K → Bool :=
  fun i => o (π.symm i)

/-- Evaluation is equivariant under the action of the symmetric group. -/
@[simp] theorem equivariant_eval (π : Equiv.Perm (Role K))
    (G : Game K L) (σ : Profile (G := G) (𝓜 := 𝓜)) :
    eval (G := permRolesGame (K := K) (L := L) π G) (𝓜 := 𝓜)
        (permProfile (K := K) (L := L) (𝓜 := 𝓜) π G σ)
      = permOutcome (K := K) π (eval (G := G) (𝓜 := 𝓜) σ) :=
  rfl

end

end KFOL
