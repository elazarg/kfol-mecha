import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax

namespace KFOL

abbrev FOLFormula (L : FirstOrder.Language) (n : ℕ) :=
  L.BoundedFormula Empty n
abbrev Sentence (L : FirstOrder.Language) := L.Sentence
abbrev Structure (L : FirstOrder.Language) := L.Structure
abbrev SortName : Type := PUnit

end KFOL
