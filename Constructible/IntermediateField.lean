import Mathlib

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {F F₁ F₂ F₃ E : IntermediateField K L}

variable (F₂) in
lemma mem_sup_left {x : L} (h : x ∈ F₁) : x ∈ F₁ ⊔ F₂ := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_left

variable (F₁) in
lemma mem_sup_right {x : L} (h : x ∈ F₂) : x ∈ F₁ ⊔ F₂ := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_right

theorem finrank_eq (h_eq : F₁ = F₂) :
    Module.finrank K F₁ = Module.finrank K F₂ := by
  subst h_eq
  rfl

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

noncomputable def finrank (h : F₁ ≤ F₂) :=
    letI : Module F₁ F₂ := (IntermediateField.inclusion h).toAlgebra.toModule
    Module.finrank F₁ F₂

theorem finrank_eq_right (h_eq : F₂ = F₃) (h_le : F₁ ≤ F₂) :
    finrank h_le = finrank (le_of_le_of_eq h_le h_eq) := by
  subst h_eq
  rfl

variable (F) in
theorem sup_le_sup_left (h : F₁ ≤ F₂) : F ⊔ F₁ ≤ F ⊔ F₂ := by gcongr

variable (F) in
def bot_le : ⊥ ≤ F := OrderBot.bot_le F

variable (F) in
theorem finrank_bot_eq : Module.finrank (⊥ : IntermediateField K L) F = Module.finrank K F := by
  rw [← @relfinrank_bot_left, relfinrank_eq_finrank_of_le (bot_le F)]
  rfl

lemma Equality_rank {F₃ : IntermediateField K L} (h : F₂ = F₃) (h1 : F₁ ≤ F₂) :
    letI : Module F₁ F₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module F₁ F₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.rank F₁ F₂ = Module.rank F₁ F₃ := by
  subst h
  rfl

variable (E) in
theorem degree_le' (h' : Module.finrank K F ≠ 0) :
    finrank (le_sup_right (a := E) (b := F)) ≤ Module.finrank K E := by
  simp only [finrank, Module.finrank, AlgHom.toRingHom_eq_coe]
  have h1 := IntermediateField.finrank_sup_le E F
  letI : Module F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra.toModule
  have h2 : Module.finrank K F * Module.finrank F ↥(E ⊔ F) = Module.finrank K ↥(E ⊔ F) :=
    Module.finrank_mul_finrank _ _ _
  rw [← h2, mul_comm] at h1
  apply Nat.le_of_mul_le_mul_right at h1
  exact h1 <| pos_of_ne_zero h'

theorem degree_le (h : F₁ ≤ F₂) (h' : finrank (le_sup_right (b := F₁) (a := F)) ≠ 0) :
    finrank (sup_le_sup_left F h) ≤ finrank h := by
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := F₁) (E := F ⊔ F₁) le_sup_right
  let FE₂ := extendScalars (F := F₁) (E := F ⊔ F₂) (le_trans h le_sup_right)
  have h_deg := degree_le' (F := FE₁) E₂
  have Eq1 : FE₂ = E₂ ⊔ FE₁ := by
    rw [IntermediateField.extendScalars_sup]
    simp [FE₂]
    congr 1
    rw [sup_comm _ F₁, ← sup_assoc]
    simp [h, sup_comm]
  specialize h_deg h'
  rwa [finrank, Equality_Degrees' Eq1.symm le_sup_right] at h_deg


instance (h_le : F₁ ≤ F₂) :
    letI : SMul F₁ F₂ := (IntermediateField.inclusion h_le).toAlgebra.toModule.toSMul
    NoZeroSMulDivisors F₁ F₂ :=
  letI : Module F₁ F₂ := (IntermediateField.inclusion h_le).toAlgebra.toModule
  Module.Free.noZeroSMulDivisors F₁ F₂

theorem rank_ne_zero_of_le (h_le : F₁ ≤ F₂) :
    letI : Module F₁ F₂ := (IntermediateField.inclusion h_le).toAlgebra.toModule
    Module.rank F₁ F₂ ≠ 0 := by
  letI : Module F₁ F₂ := (IntermediateField.inclusion h_le).toAlgebra.toModule
  simp only [AlgHom.toRingHom_eq_coe, ne_eq, rank_eq_zero_iff, smul_eq_zero, Subtype.exists,
    Subtype.forall, not_forall, not_exists, not_and, not_or]
  use 1
  refine Exists.intro (IntermediateField.one_mem F₂) ?_
  exact fun _ _ hx ↦ ⟨hx, ne_zero_of_eq_one rfl⟩

variable (E F) in
theorem rank_sup_le_rank (h : Algebra.IsAlgebraic K F) :
    letI : Module E ↥(F ⊔ E) := (IntermediateField.inclusion le_sup_right).toAlgebra.toModule
    Module.rank E ↥(F ⊔ E) ≤ Module.rank K F := by
  have := IntermediateField.adjoin_rank_le_of_isAlgebraic_right E F
  convert this using 1
  let FE := restrictScalars (L' := E) (E := adjoin E (F : Set L)) K
  have eq : F ⊔ E = FE := by
    rw [sup_comm]
    simp [restrictScalars_adjoin_eq_sup, FE]
  have HEFE : E ≤ FE := by
    rw [← eq]
    exact le_sup_right
  letI : Module E FE := (IntermediateField.inclusion (HEFE)).toAlgebra.toModule
  letI : Module E ↥(F ⊔ E) := (IntermediateField.inclusion le_sup_right).toAlgebra.toModule
  have : Module.rank E ↥(F ⊔ E) = Module.rank ↥E FE := by
    simp only [FE, Equality_rank eq]
  rw [this]
  exact rfl

theorem rank_lt_aleph0 (h : Module.rank K F < Cardinal.aleph0) :
    letI : Module E ↥(F ⊔ E) := (IntermediateField.inclusion le_sup_right).toAlgebra.toModule
    Module.rank E ↥(F ⊔ E) < Cardinal.aleph0 := by
  have : Algebra.IsAlgebraic K F := by
      rw [Module.rank_lt_aleph0_iff] at h
      exact Algebra.IsAlgebraic.of_finite (R := K) (A := F)
  exact lt_of_le_of_lt (rank_sup_le_rank F E this) h

variable (E) in
theorem finrank_ne_zero (h' : Module.finrank K F ≠ 0) :
    finrank (le_sup_right (a := F) (b := E)) ≠ 0 := by
  rw [finrank]
  letI : Module E ↥(F ⊔ E) := (IntermediateField.inclusion le_sup_right).toAlgebra.toModule
  have : Module.Free E ↥(F ⊔ E) := Module.Free.of_divisionRing E ↥(F ⊔ E)
  rw [@Nat.ne_zero_iff_zero_lt, Module.finrank, Cardinal.toNat_pos] at h' ⊢
  refine ⟨rank_ne_zero_of_le le_sup_right, rank_lt_aleph0 h'.2⟩

def DegLeTwoExtension (h_le : F₁ ≤ F₂) : Prop := finrank h_le ∣ 2

lemma degLeTwoExtension_iff_ne_le (h_le : F₁ ≤ F₂) :
    DegLeTwoExtension h_le ↔ finrank h_le ≠ 0 ∧ finrank h_le ≤ 2 := by
  rw [DegLeTwoExtension]
  constructor
  · exact fun h ↦ ⟨fun _ ↦ by simp_all, Nat.le_of_dvd Nat.zero_lt_two h⟩
  · rw [Nat.dvd_prime Nat.prime_two]
    omega

lemma degLeTwoExtension_ne_zero (h_le : F₁ ≤ F₂) (h : DegLeTwoExtension h_le) :
    finrank h_le ≠ 0 := by
  rw [degLeTwoExtension_iff_ne_le] at h
  exact h.1

variable (F) in
lemma le_adjoin (x : L) : F ≤ (IntermediateField.adjoin F {x}).restrictScalars K := by
  simp [restrictScalars_adjoin_eq_sup]

open Polynomial

lemma integral {x : L} {F : IntermediateField K L} (h : x ^ 2 ∈ F) : IsIntegral F x := by
  have : ∃ (a : F), x ^ 2 = a := by simpa
  obtain ⟨a, ha⟩ := this
  use X ^ 2 - C a
  constructor
  · monicity!
  · simp [ha]

lemma square_min_poly {x : L} {F : IntermediateField K L} (h : x ^ 2 ∈ F) :
    (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 := by
  have : ∃ (a : F), x ^ 2 = a := by simpa
  obtain ⟨a, ha⟩ := this
  let f := (X ^ 2 - C a : Polynomial F)
  let p := minpoly F x
  have hf : f ≠ 0 := by
    suffices : natDegree f > 0
    · exact ne_zero_of_natDegree_gt this
    · simp_all [f]
  have hp : p ≠ 0 := minpoly.ne_zero (integral h)
  have hf_deg : degree f = natDegree f := degree_eq_natDegree hf
  have hf_deg2 : natDegree f = 2 := by simp [f]
  rw [hf_deg2] at hf_deg
  have hp_deg : degree p = natDegree p := by exact degree_eq_natDegree hp
  have Hdeg : 0 < p.degree ∧ p.degree ≤ f.degree := by
    constructor
    · rw [hp_deg]
      rw [←gt_iff_lt]
      have : p.natDegree > 0 := by
        exact minpoly.natDegree_pos (integral h)
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

lemma degLeTwoExtension_adjoin_square_root {x : L} (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (le_adjoin F x) := by
  simp only [DegLeTwoExtension, finrank, AlgHom.toRingHom_eq_coe]
  have h1 := adjoin.finrank (integral h)
  have h2 := square_min_poly h
  rw [← h1] at h2
  rw [Nat.dvd_prime Nat.prime_two]
  convert h2

end IntermediateField
