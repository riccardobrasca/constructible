import Mathlib
import Constructible.alphadegree
import Constructible.IntermediateField

open Fin RelSeries Polynomial IntermediateField Rel

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {F : IntermediateField K L}

local notation3 "ρ" => {(F₁, F₂) : IntermediateField K L × IntermediateField K L |
  ∃ h : F₁ ≤ F₂, DegLeTwoExtension h}

variable (K L) in
def QuadraticTower := RelSeries ρ

namespace QuadraticTower

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

def relHom_comp (h : Module.finrank K F ≠ 0) : Rel.Hom ρ ρ where
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

variable (T) in
noncomputable def totalDegree := finrank (head_le_last T)

variable (F) in
lemma totalDegree_singleton : totalDegree (singleton ρ F) = 1 := by
  simp [totalDegree, finrank]
  have : (singleton ρ F).head = (singleton ρ F).last := rfl
  rw [Equality_Degrees this (le_of_eq this)]
  exact Module.finrank_self (singleton ρ F).last

variable (T) (F) in
lemma totalDegree_snoc (h : T.last ~[ρ] F) :
    totalDegree (snoc T F h) = totalDegree T * finrank h.1 := by
  simp [totalDegree, finrank]
  letI : Algebra (T.head) (T.last) := (IntermediateField.inclusion (head_le_last T)).toAlgebra
  letI : Algebra (T.last) F := (IntermediateField.inclusion h.1).toAlgebra
  letI : Algebra (T.head) F := (IntermediateField.inclusion ((le_trans T.head_le_last h.1))).toAlgebra
  have : IsScalarTower T.head T.last F := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  letI : Module (T.head) (T.last) := (IntermediateField.inclusion (head_le_last T)).toAlgebra.toModule
  letI : Module (T.last) F := (IntermediateField.inclusion h.1).toAlgebra.toModule
  letI : Module (T.head) F := (IntermediateField.inclusion ((le_trans T.head_le_last h.1))).toAlgebra.toModule
  have : Module.finrank T.head T.last * Module.finrank T.last F = Module.finrank T.head F :=
    Module.finrank_mul_finrank _ _ _
  rw [this, Equality_Degrees, Equality_Degrees']
  · rw [last_snoc]
  · rw [head_snoc]
  · exact head_le_last (T.snoc F h)

end QuadraticTower

variable (K) in
inductive IsConstructible : L → Prop
  | base (α : K) : IsConstructible (algebraMap K L α)
  | add (α β : L) : IsConstructible α → IsConstructible β → IsConstructible (α + β)
  | neg (α : L) : IsConstructible α → IsConstructible (-α)
  | mul (α β : L) : IsConstructible α → IsConstructible β → IsConstructible (α * β)
  | inv (α : L) : IsConstructible α → IsConstructible α⁻¹
  | rad (α : L) : IsConstructible (α ^ 2) → IsConstructible α

open QuadraticTower in
lemma exists_tower {x : L} (hx : IsConstructible K x) : ∃ (T : QuadraticTower K L), T.head = ⊥ ∧
    x ∈ T.last := by
  induction hx with
  | base a =>
    use RelSeries.singleton _ ⊥
    simpa using IntermediateField.algebraMap_mem ⊥ a
  | add a b ha hb hTa hTb =>
    obtain ⟨T₁, hT₁, hTa⟩ := hTa
    obtain ⟨T₂, hT2, hTb⟩ := hTb
    have h1 : Module.finrank K T₁.last ≠ 0 := by
      apply finrank_last_ne_zero
      rw [← finrank_bot_eq]
      rw [Equality_Degrees' hT₁]
      simp
      exact IntermediateField.bot_le (head T₁)
    use QuadraticTower.compose h1 hT2
    simp [QuadraticTower.compose]
    refine ⟨hT₁, ?_⟩
    simp [map_compositum, relHom_comp]
    refine IntermediateField.add_mem (RelSeries.last T₁ ⊔ RelSeries.last T₂) (mem_sup_left _ hTa ) (mem_sup_right _  hTb)
  | neg a ha hT =>
    convert hT using 3
    simp
  | mul a b ha hb hTa hTb => --same ass add
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

open QuadraticTower

lemma Tower_Degree_pow_2 (T : QuadraticTower K L): T.totalDegree ∣ 2 ^ T.length := by
  induction T using inductionOn' with
  | singleton F =>
      simpa using totalDegree_singleton F
  | snoc T F hLF h =>
      simp [pow_add,totalDegree_snoc]
      exact Nat.mul_dvd_mul h hLF.2

instance {F E : Type*} [Field F] [Field E] [Algebra F E] (K : IntermediateField F E) :
    IsScalarTower F (⊥ : IntermediateField F E) K :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

set_option synthInstance.maxHeartbeats 40000 in
lemma rank_bot'' {F E : Type*} [Field F] [Field E] [Algebra F E] (K : IntermediateField F E) :
  Module.rank (⊥ : IntermediateField F E) K = Module.rank F K := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) K, IntermediateField.rank_bot, one_mul]

@[simp]
lemma finrank_bot'' {F E : Type*} [Field F] [Field E] [Algebra F E]
  (K : IntermediateField F E) :
  Module.finrank ((⊥ : IntermediateField F E)) ↥K = Module.finrank F ↥K :=
  congr(Cardinal.toNat $(rank_bot'' K))

theorem degree_three_not_cons (x : L) (hx : Module.finrank K (adjoin K {x}) = 3) : ¬(IsConstructible K x) := by
  intro h
  have h' := exists_tower h
  rcases h' with ⟨a, b, c⟩
  refine three_not_dvd_two_pow a.length ?_
  have H := Tower_Degree_pow_2 a
  apply dvd_trans _ H
  simp [totalDegree, finrank]
  --rw [Equality_Degrees b (head_le_last a)]
  have : (adjoin K {x}) ≤ a.last := adjoin_simple_le_iff.mpr c
  have := finrank_dvd_of_le_right this
  rw [hx, ← finrank_bot'] at this
  convert this
  rw [Equality_Degrees b (head_le_last a)]
  simp

-- the cube root of 2
local notation "α" => (2 : ℂ)^((1 : ℂ)/3)

theorem cannot_double_cube : ¬(IsConstructible ℚ α) := by
  exact degree_three_not_cons α alpha_degree
