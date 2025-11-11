import KFOL.Core.Language

namespace KFOL

abbrev Role (K : ℕ) := Fin K

structure Binder (K : ℕ) (L : FirstOrder.Language) where
  role : Role K
  name : String
  sortName : SortName

abbrev Terminal (K : ℕ) (L : FirstOrder.Language) : Type _ := Role K → L.Sentence

structure Game (K : ℕ) (L : FirstOrder.Language) where
  binders : List (Binder K L)
  terminal : Terminal K L

/-– Indices for binder occurrences in the prefix of a game. -/
abbrev MoveIx {K L} (G : Game K L) := Fin G.binders.length

end KFOL
