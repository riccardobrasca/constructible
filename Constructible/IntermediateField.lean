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

lemma Equality_rank {F₁ F₂ F₃ : IntermediateField K L} (h : F₂ = F₃) (h1 : F₁ ≤ F₂) :
    letI : Module F₁ F₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module F₁ F₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.rank F₁ F₂ = Module.rank F₁ F₃ := by
  subst h
  rfl

set_option maxHeartbeats 0 in
theorem degree_finite (E : IntermediateField K L) {F : IntermediateField K L}
    (h' : Module.finrank K F ≠ 0) : finrank (le_sup_right (a := F) (b := E)) ≠ 0 := by
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
    /-
    let FE := extendScalars (F := E) (E := F ⊔ E) le_sup_right
    have : Module.rank ↥E ↥(F ⊔ E) =  Module.rank ↥E FE := by
      simp [FE]
      congr
    have : adjoin ↥E ↑F = FE := by
      simp [FE]

      sorry
    rw [this] -/



    --have := IntermediateField.rank_sup_le F E
    --maybe this is the thing Subalgebra.adjoin_rank_le
    --better use IntermediateField.adjoin_rank_le_of_isAlgebraic
    --have : Module.Free K F := sorry
    /- let E' := E.toSubalgebra
    let F' := F.toSubalgebra
    have := Subalgebra.adjoin_rank_le (F := K) (K := L) E' F'


    have := lt_of_le_of_lt this h'.2
    apply lt_of_le_of_lt _ this

    simp [E', F']
 -/
    rw [this]
    exact rfl

    --rw [@Submodule.rank_eq_spanRank_of_free]

    /-
    rw [ Module.rank_lt_aleph0_iff] at h' ⊢
    obtain ⟨s, hs⟩:= h'.2
    let m : F ↪ (F ⊔ E : IntermediateField K L) := by
      have : F ≤ (F ⊔ E : IntermediateField K L) := le_sup_left
      exact Subtype.impEmbedding (Membership.mem F) (Membership.mem (F ⊔ E)) this
    use s.map m
    simp only [AlgHom.toRingHom_eq_coe]
    rw [@Submodule.eq_top_iff'] at hs ⊢
    simp
    intro a ha
    rw [IntermediateField.sup_def] at ha
    rw [adjoin] at ha
    simp [Subfield.closure] at ha -/


    --rw [← restrictScalars_adjoin] at ha
    /- rw [mem_adjoin_iff_div] at ha
    obtain ⟨f, hf, g, hg, ha⟩ := ha
    subst ha
-/

    --rw [@Submodule.mem_span_image_iff_exists_fun]

    --simp
    --IntermediateField.sup_def

  --apply Module.finrank_pos
  --Module.rank_lt_aleph0_iff



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


end IntermediateField
