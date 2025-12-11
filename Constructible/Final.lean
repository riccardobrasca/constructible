import Mathlib

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

theorem finrank_eq (h_eq : F₁ = F₂) : Module.finrank K F₁ = Module.finrank K F₂ := by grind



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
  rwa [← h2, mul_comm, mul_le_mul_iff_left₀ (pos_of_ne_zero h')] at h1

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




def DegLeTwoExtension (h_le : F₁ ≤ F₂) : Prop := IntermediateField.finrank h_le ∣ 2

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


local notation3 "ρ" => {(F₁, F₂) : IntermediateField K L × IntermediateField K L |
  ∃ h : F₁ ≤ F₂, DegLeTwoExtension h}

variable (K L) in
def QuadraticTower := RelSeries ρ


namespace QuadraticTower

open IntermediateField RelSeries SetRel

variable {T T₁ T₂ : QuadraticTower K L}

theorem finrank_last_ne_zero (h : Module.finrank K T.head ≠ 0) : Module.finrank K T.last ≠ 0 := by
  induction T using inductionOn' with
  | singleton _ =>
    exact h
  | snoc T F hF hT =>
    rw [finrank_eq (head_snoc T F hF)] at h
    specialize hT h
    have h_eq : (T.snoc F hF).last = F := by
      rw [last_snoc]
    letI : Module T.last F := (IntermediateField.inclusion hF.1).toAlgebra.toModule
    have h_mul : Module.finrank K T.last * Module.finrank T.last F = Module.finrank K F :=
      Module.finrank_mul_finrank K T.last F
    rw [finrank_eq h_eq, ← h_mul]
    refine Nat.mul_ne_zero hT <| degLeTwoExtension_ne_zero hF.1 hF.2

def relHom_comp (h : Module.finrank K F ≠ 0) : SetRel.Hom ρ ρ where
  toFun E := F ⊔ E
  map_rel' := by
    intro E₁ E₂ hr
    obtain ⟨hr₁, hr₂⟩ := hr
    refine ⟨IntermediateField.sup_le_sup_left F hr₁, ?_⟩
    rw [degLeTwoExtension_iff_ne_le, finrank] at hr₂ ⊢
    constructor
    · let E₂' := extendScalars hr₁
      let FE₁ := extendScalars (F := E₁) (E := F ⊔ E₁) le_sup_right
      let FE₂ := extendScalars (F := E₁) (E := F ⊔ E₂) (le_trans hr₁ le_sup_right)
      have hdeg := finrank_ne_zero (F := E₂') FE₁ hr₂.1
      have heq : E₂' ⊔ FE₁ = FE₂ := by
        rw [extendScalars_sup]
        congr 1
        rw [sup_comm E₂, sup_assoc]
        simp [hr₁]
      rwa [finrank, Equality_Degrees' heq] at hdeg
    · exact le_trans (degree_le hr₁ (finrank_ne_zero E₁ h)) hr₂.2

variable (T) in
def map_compositum (h : Module.finrank K F ≠ 0) : QuadraticTower K L := T.map (relHom_comp h)

def compose (h1 : Module.finrank K T₁.last ≠ 0) (h2 : T₂.head = ⊥) :
    QuadraticTower K L := append T₁ (T₂.map_compositum h1) (by
  simp only [Set.mem_setOf_eq]
  constructor
  · rw [degLeTwoExtension_iff_ne_le, finrank]
    simp only [map_compositum, relHom_comp, Set.mem_setOf_eq, head_map, RelHom.coeFn_mk,
      AlgHom.toRingHom_eq_coe, ne_eq]
    have : RelSeries.last T₁ ⊔ head T₂ = RelSeries.last T₁ := by
      rw [h2]
      exact sup_bot_eq (RelSeries.last T₁)
    rw [Equality_Degrees' this le_sup_left]
    simp
  · simp [map_compositum, relHom_comp])

/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
variable (T) in
lemma head_le_last : T.head ≤ T.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  induction T using RelSeries.inductionOn' with
  | singleton x =>
    simp
  | snoc p x hx hp =>
    simp only [snoc_length, last_snoc']
    rw [apply_zero, head_snoc, ← apply_zero]
    have h2 : p.toFun (Fin.last p.length) = p.last := rfl
    rw [h2] at hp
    exact le_trans hp hx.1

end QuadraticTower

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {F₁ F₂ : IntermediateField K L}

variable (K) in
inductive IsConstructible : L → Prop
  | base (α : K) : IsConstructible (algebraMap K L α)
  | add (α β : L) : IsConstructible α → IsConstructible β → IsConstructible (α + β)
  | neg (α : L) : IsConstructible α → IsConstructible (-α)
  | mul (α β : L) : IsConstructible α → IsConstructible β → IsConstructible (α * β)
  | inv (α : L) : IsConstructible α → IsConstructible α⁻¹
  | rad (α : L) : IsConstructible (α ^ 2) → IsConstructible α



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


open QuadraticTower RelSeries in
lemma exists_tower {x : L} (hx : IsConstructible K x) : ∃ (T : QuadraticTower K L), T.head = ⊥ ∧
    x ∈ T.last := by
  induction hx with
  | base a =>
    use RelSeries.singleton _ ⊥
    simp
  | add a b ha hb hTa hTb =>
    obtain ⟨T₁, hT₁, hTa⟩ := hTa
    obtain ⟨T₂, hT2, hTb⟩ := hTb
    have h1 : Module.finrank K T₁.last ≠ 0 := by
      apply finrank_last_ne_zero
      rw [← finrank_bot_eq]
      rw [Equality_Degrees' hT₁]
      simp
      exact IntermediateField.bot_le T₁.head
    use QuadraticTower.compose h1 hT2
    simp [QuadraticTower.compose]
    refine ⟨hT₁, ?_⟩
    simp [map_compositum, relHom_comp]
    refine IntermediateField.add_mem (RelSeries.last T₁ ⊔ RelSeries.last T₂) (mem_sup_left _ hTa ) (mem_sup_right _  hTb)
  | neg a ha hT =>
    convert hT using 3
    simp
  | mul a b ha hb hTa hTb => --same as add
    obtain ⟨T₁, hT₁, hTa⟩ := hTa
    obtain ⟨T₂, hT₂, hTb⟩ := hTb
    have h1 : Module.finrank K T₁.last ≠ 0 := by
      apply finrank_last_ne_zero
      rw [← finrank_bot_eq]
      rw [Equality_Degrees' hT₁]
      simp
      exact IntermediateField.bot_le (head T₁)
    use QuadraticTower.compose h1 hT₂
    simp [QuadraticTower.compose]
    refine ⟨hT₁, ?_⟩
    simp [map_compositum, relHom_comp]
    refine IntermediateField.mul_mem (RelSeries.last T₁ ⊔ RelSeries.last T₂) (mem_sup_left _ hTa ) (mem_sup_right _ hTb)
  | inv a ha hT=>
    convert hT using 3
    simp
  | rad a ha hT =>
    obtain ⟨T, hQ, hl⟩ := hT
    let F := (IntermediateField.adjoin T.last {a}).restrictScalars K
    have h_le : T.last ≤ F := by
      have := adjoin_contains_field_as_subfield {a} T.last.toSubfield
      simpa using this
    have h2 : DegLeTwoExtension h_le := by
      exact degLeTwoExtension_adjoin_square_root hl
    have hr : ∃ h : T.last ≤ F, DegLeTwoExtension h := by use h_le
    use RelSeries.snoc T F hr
    constructor
    · rwa [head_snoc]
    · rw [last_snoc]
      simp [F]
      exact mem_adjoin_simple_self T.last a


end IntermediateField
