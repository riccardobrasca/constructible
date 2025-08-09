import Constructible.Lemmas

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {F F₁ F₂ E : IntermediateField K L}

variable (F₂) in
lemma mem_sup_left {x : L} (h : x ∈ F₁) : x ∈ F₁ ⊔ F₂ := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_left

variable (F₁) in
lemma mem_sup_right {x : L} (h : x ∈ F₂) : x ∈ F₁ ⊔ F₂ := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_right

noncomputable def finrank (h : F₁ ≤ F₂) :=
    letI : Module F₁ F₂ := (IntermediateField.inclusion h).toAlgebra.toModule
    Module.finrank F₁ F₂

variable (F) in
theorem sup_le_sup_left (h : F₁ ≤ F₂) : F ⊔ F₁ ≤ F ⊔ F₂ := by gcongr

variable (F) in
def bot_le : ⊥ ≤ F := OrderBot.bot_le F

variable (F) in
theorem finrank_bot_eq : Module.finrank (⊥ : IntermediateField K L) F = Module.finrank K F := by
  rw [← @relfinrank_bot_left, relfinrank_eq_finrank_of_le (bot_le F)]
  rfl


variable (E) in
theorem degree_le' (h' : Module.finrank K F ≠ 0) :
    finrank (le_sup_right (a := E) (b := F)) ≤ Module.finrank K E := by
  have h1 := IntermediateField.finrank_sup_le E F
  letI : Module ↥F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra.toModule
  have h2 : Module.finrank K ↥F * Module.finrank ↥F ↥(E ⊔ F) = Module.finrank K ↥(E ⊔ F) :=
    Module.finrank_mul_finrank _ _ _
  simp [finrank]
  rw [← h2, mul_comm] at h1
  field_simp [h'] at h1
  exact h1

lemma Equality_rank {F₃ : IntermediateField K L} (h : F₂ = F₃) (h1 : F₁ ≤ F₂) :
    letI : Module F₁ F₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module F₁ F₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.rank F₁ F₂ = Module.rank F₁ F₃ := by
  subst h
  rfl

set_option maxHeartbeats 0 in
variable (E) in
theorem degree_finite (E : IntermediateField K L) (h' : Module.finrank K F ≠ 0) :
    finrank (le_sup_right (a := F) (b := E)) ≠ 0 := by
  rw [finrank]
  letI : Module ↥E ↥(F ⊔ E) := (IntermediateField.inclusion le_sup_right).toAlgebra.toModule
  have : Module.Free ↥E ↥(F ⊔ E) := Module.Free.of_divisionRing ↥E ↥(F ⊔ E)
  --have := Module.rank_lt_aleph0_iff (R := E) (M := (F ⊔ E : IntermediateField K L))
  rw [@Nat.ne_zero_iff_zero_lt, Module.finrank, Cardinal.toNat_pos] at h' ⊢
  constructor
  · --this is too complicated, simplyfy (or better make a lemma in general)
    simp only [AlgHom.toRingHom_eq_coe, ne_eq]
    rw [rank_eq_zero_iff]
    simp
    use 1
    refine Exists.intro ?_ ?_
    exact IntermediateField.one_mem (F ⊔ E)
    intro x hx hxx
    refine ⟨hxx, ?_⟩
    exact ne_zero_of_eq_one rfl
  · have : Algebra.IsAlgebraic K ↥F := by
      rw [Module.rank_lt_aleph0_iff] at h'
      have := h'.2
      exact Algebra.IsAlgebraic.of_finite (R := K) (A := F)
    have := IntermediateField.adjoin_rank_le_of_isAlgebraic_right E F
    have := lt_of_le_of_lt this h'.2
    convert this using 1
    let FE := restrictScalars (L' := E) (E := adjoin ↥E (F : Set L)) K
    have eq : F ⊔ E = FE := by
      simp [FE, restrictScalars_adjoin_eq_sup]
      rw [sup_comm]
    have HEFE : E ≤ FE := by
      apply le_trans (le_sup_right (a := F))
      simp only [FE]
      rw [restrictScalars_adjoin_eq_sup, sup_comm]
      gcongr
      apply le_of_eq
      exact Eq.symm (adjoin_self K F)
    letI : Module ↥E ↥FE := (IntermediateField.inclusion (HEFE)).toAlgebra.toModule

    have : Module.rank ↥E ↥(F ⊔ E) = Module.rank ↥E FE := by
      simp [FE]
      rw [Equality_rank eq]
    rw [this]
    exact rfl


--set_option maxHeartbeats 0 in --try to make this faster
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


def DegLeTwoExtension (h_le : F₁ ≤ F₂) : Prop := finrank h_le ∣ 2

lemma degLeTwoExtension_iff_ne_le (h_le : F₁ ≤ F₂) :
    DegLeTwoExtension h_le ↔ finrank h_le ≠ 0 ∧ finrank h_le ≤ 2 := by
  rw [DegLeTwoExtension]
  constructor
  · intro h
    exact ⟨fun _ ↦ by simp_all, Nat.le_of_dvd Nat.zero_lt_two h⟩
  · rw [Nat.dvd_prime Nat.prime_two]
    omega

lemma degLeTwoExtension_ne_zero (h_le : F₁ ≤ F₂) (h : DegLeTwoExtension h_le) :
    finrank h_le ≠ 0 := by
  rw [degLeTwoExtension_iff_ne_le] at h
  exact h.1

variable (F) in
lemma le_adjoin (x : L) : F ≤ (IntermediateField.adjoin F {x}).restrictScalars K := by
  simp [restrictScalars_adjoin_eq_sup]

lemma degLeTwoExtension_adjoin_square_root {x : L} (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (le_adjoin F x) := by
  simp only [DegLeTwoExtension, finrank, AlgHom.toRingHom_eq_coe]
  have h1 := adjoin.finrank (integral x F h)
  have h2 := square_min_poly x F h
  rw [← h1] at h2
  rw [Nat.dvd_prime Nat.prime_two]
  convert h2

end IntermediateField
