import Constructible.Constructible

open Fin RelSeries Polynomial IntermediateField SetRel

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {F : IntermediateField K L}

lemma IsConstructible_of_exists_tower {x : L} (hx : ∃ (T : QuadraticTower K L), T.head = ⊥ ∧
    x ∈ T.last ) : IsConstructible K x:= by
  sorry
