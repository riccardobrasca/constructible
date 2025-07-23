import Mathlib

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/- lemma ciao (C : RelSeries {(x, y) : IntermediateField K L × IntermediateField K L | x ≤ y})
    {i : Fin (C.length + 1)} (hi : i < Fin.last C.length) :
    C.toFun i ≤ C.toFun (i+1) := C.rel_of_lt <|Fin.lt_add_one_iff.mpr hi -/

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

open Polynomial IntermediateField Rel

lemma integral (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) : IsIntegral F x := by
  have : ∃ (a : F), x ^ 2 = ↑a := by
    simp
    exact h
  obtain ⟨a, ha⟩ := this
  let f := (X ^ 2 - C a : Polynomial F)
  use f
  have H : (aeval x) f = 0 := by
    simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C,
    IntermediateField.algebraMap_apply, sub_self, f]
  constructor
  · monicity
    simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, sub_self,
      Nat.ofNat_pos, leadingCoeff_X_pow_sub_C, f]
  · exact H

lemma square_min_poly (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) :
    (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 := by
  have : ∃ (a : F), x ^ 2 = (a : L) := by
    simp
    exact h
  obtain ⟨a, ha⟩ := this
  let f := (X ^ 2 - C a : Polynomial F)
  let p := minpoly (↑F) x
  have hf : f ≠ 0 := by
    suffices : natDegree f > 0
    · exact ne_zero_of_natDegree_gt this
    · simp_all only [SetLike.coe_mem, natDegree_sub_C, natDegree_pow,
        natDegree_X, mul_one, gt_iff_lt, Nat.ofNat_pos, f]
  have h_int : IsIntegral F x := by
    exact integral x F h
  have hp : p ≠ 0 := by
    suffices : natDegree p > 0
    · exact ne_zero_of_natDegree_gt this
    · exact minpoly.natDegree_pos (integral x F h)
  have hf_deg : degree f = natDegree f := by exact degree_eq_natDegree hf
  have hf_deg2 : natDegree f = 2 := by
    simp_all only [SetLike.coe_mem, ne_eq, natDegree_sub_C, natDegree_pow,
      natDegree_X, mul_one, Nat.cast_ofNat, f, p]
  rw [hf_deg2] at hf_deg
  have hp_deg : degree p = natDegree p := by exact degree_eq_natDegree hp
  have Hdeg : 0 < p.degree ∧ p.degree ≤ f.degree := by
    constructor
    · rw [hp_deg]
      rw [←gt_iff_lt]
      have : p.natDegree > 0 := by
        exact minpoly.natDegree_pos h_int
      simp_all only [SetLike.coe_mem, ne_eq, Nat.cast_ofNat, natDegree_sub_C,
        natDegree_pow, natDegree_X, mul_one, gt_iff_lt, Nat.cast_pos, p, f]
    · apply minpoly.min
      · monicity
        rw [leadingCoeff_X_pow_sub_C (Nat.le.step Nat.le.refl)]
      · simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C,
        IntermediateField.algebraMap_apply, sub_self, f]
  rw [hf_deg] at Hdeg
  have test := Hdeg
  cases' Hdeg : p.degree with n
  · simp_all [p, f]
  · rw [hp_deg] at test
    rw [hp_deg] at Hdeg
    rw [Hdeg] at test
    rw [Hdeg] at hp_deg
    suffices : p.natDegree = 1 ∨ p.natDegree = 2
    · simp_all only [SetLike.coe_mem, ne_eq, Nat.cast_ofNat, natDegree_sub_C,
        natDegree_pow, natDegree_X, mul_one, WithBot.coe_pos, p, f]
    · rcases test with ⟨hn_pos, hn_le⟩
      have hn_pos' : 0 < n := by
        exact WithBot.coe_pos.mp hn_pos
      have hn_le' : n ≤ 2 := by
        exact WithBot.coe_le_coe.mp hn_le
      have testest : p.natDegree = n := by
        exact (degree_eq_iff_natDegree_eq_of_pos hn_pos').mp hp_deg
      interval_cases n
      · left
        exact testest
      · right
        exact testest

-- this should be in mathlib? I couldn't find it anywhere
@[simp]
theorem restrictScalars_extendScalars {K : Type u_1} {L : Type u_2} [Field K] [Field L]
    [Algebra K L] (L' : IntermediateField K L) (E : IntermediateField L' L)
    (h : L' ≤ restrictScalars K E) : extendScalars h = E := by
  rfl

lemma blah (x : L) (F : IntermediateField K L) :
        F ≤ (IntermediateField.adjoin F {x}).restrictScalars K := by
  rw [restrictScalars_adjoin_eq_sup]
  simp
