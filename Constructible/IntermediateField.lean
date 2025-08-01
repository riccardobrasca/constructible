import Constructible.Lemmas

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma mem_sup_left {F E : IntermediateField K L} {x : L} (h : x ∈ F) :
    x ∈ F ⊔ E := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_left

lemma mem_sup_right {F E : IntermediateField K L} {x : L} (h : x ∈ E) :
    x ∈ F ⊔ E := by
  rw [← @adjoin_simple_le_iff] at h ⊢
  exact le_trans h le_sup_right

noncomputable def finrank {F₁ F₂ : IntermediateField K L} (h : F₁ ≤ F₂) :=
    letI : Module F₁ F₂ := (IntermediateField.inclusion h).toAlgebra.toModule
    Module.finrank F₁ F₂

/-
theorem comp_ne_zero {E F G : IntermediateField K L} {hLE1 : E ≤ F} {hLE2 : F ≤ G} (hd1 : finrank hLE1 ≠ 0)
    (hd2 : finrank hLE2 ≠ 0) : finrank (le_trans hLE1 hLE2) ≠ 0 := by

  sorry -/

def DegLeTwoExtension {F₁ F₂ : IntermediateField K L} (h_le : F₁ ≤ F₂) : Prop :=
  finrank h_le ∣ 2

lemma degLeTwoExtension_iff_ne_le {F₁ F₂ : IntermediateField K L} (h_le : F₁ ≤ F₂) :
    DegLeTwoExtension h_le ↔ finrank h_le ≠ 0 ∧ finrank h_le ≤ 2 := by
  rw [DegLeTwoExtension]
  constructor
  · intro h
    exact ⟨fun _ ↦ by simp_all, Nat.le_of_dvd Nat.zero_lt_two h⟩
  · rw [Nat.dvd_prime Nat.prime_two]
    omega

lemma degLeTwoExtension_ne_zero {F₁ F₂ : IntermediateField K L} (h_le : F₁ ≤ F₂)
    (h : DegLeTwoExtension h_le) : finrank h_le ≠ 0 := by
  rw [degLeTwoExtension_iff_ne_le] at h
  exact h.1

lemma le_adjoin (x : L) (F : IntermediateField K L) :
        F ≤ (IntermediateField.adjoin F {x}).restrictScalars K := by
  simp [restrictScalars_adjoin_eq_sup]

lemma degLeTwoExtension_adjoin_square_root {x : L} {F : IntermediateField K L} (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (le_adjoin x F) := by
  simp only [DegLeTwoExtension, finrank, AlgHom.toRingHom_eq_coe]
  have h1 := adjoin.finrank (integral x F h)
  have h2 := square_min_poly x F h
  rw [← h1] at h2
  rw [Nat.dvd_prime Nat.prime_two]
  convert h2

theorem sup_le_sup_left (f : IntermediateField K L) {e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
     f ⊔ e₁ ≤ f ⊔ e₂ := by
  gcongr

def bot_le (F : IntermediateField K L) : ⊥ ≤ F := OrderBot.bot_le F

theorem finrank_bot_eq (F : IntermediateField K L) :
    Module.finrank (⊥ : IntermediateField K L) F = Module.finrank K F := by
  rw [← @relfinrank_bot_left, relfinrank_eq_finrank_of_le (bot_le F)]
  rfl

--set_option maxHeartbeats 0 in
theorem degree_le' (E : IntermediateField K L) {F : IntermediateField K L}
    (h' : Module.finrank K F ≠ 0) :
    finrank (le_sup_right (a := E) (b := F)) ≤ Module.finrank K E := by
  have h1 := IntermediateField.finrank_sup_le E F
  letI : Module ↥F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra.toModule
  have h2 : Module.finrank K ↥F * Module.finrank ↥F ↥(E ⊔ F) = Module.finrank K ↥(E ⊔ F) :=
    Module.finrank_mul_finrank _ _ _
  simp [finrank]
  rw [← h2, mul_comm] at h1
  field_simp [h'] at h1
  exact h1

theorem degree_finite (E : IntermediateField K L) {F : IntermediateField K L}
    (h' : Module.finrank K F ≠ 0) : finrank (le_sup_right (a := F) (b := E)) ≠ 0 := by

  sorry

--set_option maxHeartbeats 0 in --try to make this faster
theorem degree_le {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂)
    (h' : finrank (le_sup_right (b := e₁) (a := f)) ≠ 0) :
    finrank (sup_le_sup_left f h) ≤ finrank h := by
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := e₁) (E := f ⊔ e₁) le_sup_right
  let FE₂ := extendScalars (F := e₁) (E := f ⊔ e₂) (le_trans h le_sup_right)
  have h_deg := degree_le' (F := FE₁) E₂
  have Eq1 : FE₂ = E₂ ⊔ FE₁ := by
    rw [IntermediateField.extendScalars_sup]
    simp [FE₂]
    congr 1
    rw [sup_comm _ e₁, ← sup_assoc]
    simp [h, sup_comm]
  specialize h_deg h'
  rwa [finrank, Equality_Degrees' Eq1.symm le_sup_right] at h_deg

/- set_option maxHeartbeats 0 in --try to make this faster
theorem degree_le {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂)
    (h' : finrank (le_sup_right (b := e₁) (a := f)) ≠ 0) :
    finrank (sup_le_sup_left f h) ≤ finrank h := by
  let E₁ := extendScalars (le_refl e₁)
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := e₁) (E := f ⊔ e₁) le_sup_right
  let FE₂ := extendScalars (F := e₁) (E := f ⊔ e₂) (le_trans h le_sup_right)
  have LE1 : FE₁ ≤ FE₂ := by
    rw [IntermediateField.extendScalars_le_extendScalars_iff]
    exact sup_le_sup_left f h
  letI := (inclusion LE1).toAlgebra.toModule
  have Eq1 : FE₂ = FE₁ ⊔ E₂ := by
    rw [IntermediateField.extendScalars_sup]
    simp [FE₂]
    congr 1
    rw [sup_assoc]
    simp_all [sup_of_le_right]
  have LE2 : FE₁ ≤ FE₁ ⊔ E₂ := le_trans LE1 <| le_of_eq Eq1
  letI := (inclusion h).toAlgebra.toModule
  letI := (inclusion LE2).toAlgebra.toModule
  have H_deg : Module.finrank ↥e₁ ↥(FE₁ ⊔ E₂) = Module.finrank ↥e₁ FE₁ * Module.finrank FE₁ ↥(FE₁ ⊔ E₂) := by
    --refine (Module.finrank_mul_finrank ?_ ?_ ?_ ?_ ?_).symm
    have :  Module.Free ↥e₁ ↥FE₁ := Module.Free.of_divisionRing ↥e₁ ↥FE₁
    have :  Module.Free ↥FE₁ ↥(FE₁ ⊔ E₂) := Module.Free.of_divisionRing ↥FE₁ ↥(FE₁ ⊔ E₂)
    /- have : IsScalarTower e₁ FE₁ (FE₁ ⊔ E₂ : IntermediateField e₁ L) := by
      sorry -/
    have a := Module.finrank_mul_finrank e₁ FE₁ (FE₁ ⊔ E₂ : IntermediateField e₁ L)
    exact id (Eq.symm a)
  have : Module.finrank FE₁ FE₂ ≤ Module.finrank E₁ E₂ := by
    rw [Equality_Degrees' Eq1]
    have key := IntermediateField.finrank_sup_le FE₁ E₂
    --have a := Module.finrank_mul_finrank e₁ e₂ (f ⊔ e₁ : IntermediateField K L)
    rw [H_deg] at key
    have : Module.finrank ↥e₁ ↥FE₁ ≠ 0 := by
      simp_all [FE₂, FE₁, E₂]
      exact h'
    field_simp [this] at key
    exact key
  assumption -/
  /- have Eq1 : f ⊔ e₂ = (f ⊔ e₁) ⊔ e₂ := by simp [sup_assoc, h]
  have LE0 := le_refl e₁
  have LE1 : e₁ ≤ f ⊔ e₁ := le_sup_right
  have LE2 : e₁ ≤ f ⊔ e₂ := le_trans h <| le_sup_right
  have LE2' : e₁ ≤ (f ⊔ e₁) ⊔ e₂ := le_trans LE1 le_sup_left
  have FLE0:= IntermediateField.finrank_sup_le (extendScalars LE1) (extendScalars LE2')
  have F1 : ↥(f ⊔ e₁ ⊔ e₂) = ↥(extendScalars LE1 ⊔ extendScalars LE2') := by sorry
  have FLE : finrank LE2' ≤ finrank h * finrank LE1 := by
    simp [finrank] --Equality_Degrees' F1
    sorry
  letI := Algebra_of_le LE1
  letI M1 := Module_of_le LE1
  letI M2 := Module_of_le (compositum_le f h)
  letI M3 := Module_of_le LE2
  --have S : IsScalarTower ↥e₁ ↥(f ⊔ e₁) ↥(f ⊔ e₂) := sorry
  --have EQ := Module.finrank_mul_finrank e₁ (f ⊔ e₁ : IntermediateField K L) (f ⊔ e₂ : IntermediateField K L)
  letI : Module (extendScalars LE1) (extendScalars LE2) := sorry
  letI : Module (extendScalars LE1) (extendScalars LE2') := sorry

  letI : SMul ↥(extendScalars LE1) ↥(extendScalars LE2') := sorry
  letI :  IsScalarTower ↥(extendScalars LE0) ↥(extendScalars LE1) ↥(extendScalars LE2') := by sorry
  letI : Module.Free (extendScalars LE0) (extendScalars LE1) := sorry
  letI : Module.Free (extendScalars LE1) (extendScalars LE2) := sorry
  --have EQ := Module.finrank_mul_finrank (extendScalars LE0) (extendScalars LE1) (extendScalars LE2')
  --have EQ := Module.finrank_mul_finrank (extendScalars LE0) (extendScalars LE1) (extendScalars LE2)
  --
  --have : IsScalarTower (extendScalars LE0) (extendScalars LE1) (extendScalars LE2) := by sorry
  simp only [ge_iff_le]
  simp only [finrank]
  rw [Equality_Degrees' Eq1]
  --have key := IntermediateField.finrank_sup_le (f ⊔ e₁) e₂
  --have := Module.finrank_mul_finrank e₁ (f ⊔ e₁ : IntermediateField K L) (f ⊔ e₂ : IntermediateField K L)
  have H_deg : finrank LE1 = finrank (@le_sup_right _ _ e₁ (f ⊔ e₁)) * finrank (compositum_le f h) := by
    sorry
  simp [finrank] at H_deg
  --rw [Equality_Degrees' Eq1] -/

end IntermediateField
