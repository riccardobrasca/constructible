import Mathlib

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma ciao (C : RelSeries {(x, y) : IntermediateField K L × IntermediateField K L | x ≤ y})
    {i : Fin (C.length + 1)} (hi : i < Fin.last C.length) :
    C.toFun i ≤ C.toFun (i+1) := C.rel_of_lt <|Fin.lt_add_one_iff.mpr hi

/-Trivial Lemma, but requires a proof for Lean-/
lemma Equality_Degrees {K L : Type*} [Field K] [Field L] [Algebra L K] {K₁ K₂ K₃ : IntermediateField L K}
    (h : K₁ = K₂) (h1 : K₁ ≤ K₃) :
    letI : Module K₁ K₃ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module K₂ K₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.finrank K₁ K₃ = Module.finrank K₂ K₃ := by
  subst h
  rfl

lemma Equality_Degrees' {K L : Type*} [Field K]  [Field L] [Algebra L K] {K₁ K₂ K₃ : IntermediateField L K}
    (h : K₂ = K₃) (h1 : K₁ ≤ K₂) :
    letI : Module K₁ K₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module K₁ K₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.finrank K₁ K₂ = Module.finrank K₁ K₃ := by
  subst h
  rfl
