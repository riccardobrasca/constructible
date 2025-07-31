import Mathlib
import Constructible.Lemmas
import Constructible.alphadegree
import Constructible.IntermediateField

open Fin RelSeries Polynomial IntermediateField Rel

variable {K L : Type*} [Field K] [Field L] [Algebra K L]


local notation3 "ρ" => {(F₁, F₂) : IntermediateField K L × IntermediateField K L |
  ∃ h : F₁ ≤ F₂, DegLeTwoExtension h}

variable (K L) in
def QuadraticTower := RelSeries ρ

namespace QuadraticTower
/-
theorem finite_degree (T : QuadraticTower K L) (i : Fin (T.length)) :
    letI := (inclusion (T.step i).2.1).toAlgebra.toModule
    Module.finrank (T.toFun (Fin.castSucc i)) (T.toFun i.succ) ≠ 0 := by
  have := (T.step i).2.2
  simp [DegLeTwoExtension] at this

  rw [Nat.dvd_prime Nat.prime_two] at this

  sorry -/
/-
theorem finite_degree_last {T : QuadraticTower K L} (hl : T.length ≠ 0) : Module.finrank K T.last ≠ 0 := by
  by_cases hl : T.length = 0
  · simp
    sorry
  let i₀ : Fin T.length := ⟨T.length - 1, by omega⟩
  have h := T.step i₀
  have h1 := h.1
  have h2 := h.2.1
  have h3 := h.2.2
  simp [DegLeTwoExtension, finrank] at h3

  sorry -/


set_option synthInstance.maxHeartbeats  0 in --try to make this faster
def relHom_comp {F : IntermediateField K L} (h : Module.finrank K F ≠ 0) : Rel.Hom ρ ρ where
  toFun x := F ⊔ x
  map_rel' := by
    intro E₁ E₂ hr
    obtain ⟨hr₁, hr₂⟩ := hr
    refine ⟨compositum_le F hr₁, ?_⟩
    rw [DegLeTwoExtension_iff_ne_le, finrank] at hr₂ ⊢
    constructor
    ·
      sorry
    ·
      have := degree_le (f := F) hr₁ (by
        rw [finrank]
        --comp finite degree

        sorry)
      simp [finrank] at this
      exact le_trans this hr₂.2
    --use compositum_le F hr₁

/-

set_option synthInstance.maxHeartbeats  0 in --try to make this faster
def relHom_comp' {F : IntermediateField K L} (h : finrank (OrderBot.bot_le F) ≠ 0) : Rel.Hom ρ ρ where
  toFun x := F ⊔ x
  map_rel' := by
    intro F₁ F₂ h
    obtain ⟨h₁, h₂⟩ := h
    use compositum_le F h₁
    have LE1 : F₁ ≤ F ⊔ F₁ := le_sup_right
    have LE2 : F ≤ F ⊔ F₁ := le_sup_left
    have LE3 : F ⊔ F₁ ≤ F ⊔ F₂ := compositum_le F h₁
    have h₃ : finrank LE1 ≠ 0 := by
      rw [@Nat.ne_zero_iff_zero_lt]
      simp [finrank]
      letI : Module F₁ (F ⊔ F₁ : IntermediateField K L) := (IntermediateField.inclusion LE1).toAlgebra.toModule
      have : Module.Free F₁ (F ⊔ F₁ : IntermediateField K L) := Module.Free.of_divisionRing _ _
      let F' := restrict LE2
      have hFFG: (F'.toSubmodule).FG := by

        sorry
      have : Module.Finite ↥F₁ ↥(F ⊔ F₁) := by
        rw [@Module.finite_def]
        obtain ⟨s, hs⟩ := hFFG
        use s
        rw [@Submodule.eq_top_iff']
        intro x hx

        sorry
      apply Module.finrank_pos
      /- simp only [finrank, Module.finrank]
      rw [@Cardinal.toNat_ne_zero]
      constructor
      ·
        sorry -/
      --rw [@Nat.ne_zero_iff_zero_lt]

      --have := rank_sup_le_of_isAlgebraic F₁ F
      --simp [Nat.ne_zero_iff_zero_lt, finrank] at h ⊢

      /- intro h₀
      apply h
      -/

      --sorry
    have := degree_le (f := F) h₁ h₃
    simp [finrank] at this

    have h₄ : finrank LE3 ≤ 2 := by
      sorry
    simp_all [DegLeTwoExtension]
    convert_to Module.finrank ↥(F ⊔ F₁) ↥(extendScalars (compositum_le F h₁)) ≤ 2 ∧ 0 < Module.finrank ↥(F ⊔ F₁) ↥(extendScalars (compositum_le F h₁))
    · rw [Nat.dvd_prime Nat.prime_two]
      omega
    · constructor
      ·
        sorry
      · apply Nat.pos_of_ne_zero
        sorry
 -/

def map_compositum (T : QuadraticTower K L) {F : IntermediateField K L} (h : Module.finrank K F ≠ 0) : QuadraticTower K L :=
  T.map (relHom_comp h)

def compose {T₁ T₂ : QuadraticTower K L} (h1 : Module.finrank K T₁.last ≠ 0) (h2 : T₂.head = ⊥) :
    QuadraticTower K L := append T₁ (T₂.map_compositum h1) (by
  simp
  constructor
  · rw [DegLeTwoExtension_iff_ne_le, finrank]
    simp [map_compositum, relHom_comp]
    have : RelSeries.last T₁ ⊔ head T₂ = RelSeries.last T₁ := by
        rw [h2]
        exact sup_bot_eq (RelSeries.last T₁)
    rw [Equality_Degrees' this le_sup_left]
    simp

  · simp [map_compositum, relHom_comp])

/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
lemma head_le_last (T : QuadraticTower K L) :
    T.head ≤ T.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  induction T using RelSeries.inductionOn' with
  | singleton x =>
    simp
  | snoc p x hx hp =>
    simp
    rw [apply_zero, head_snoc, ← apply_zero]
    have h2 : p.toFun (Fin.last p.length) = p.last := rfl
    rw [h2] at hp
    exact le_trans hp hx.1

noncomputable def totalDegree (T : QuadraticTower K L) : ℕ := finrank (head_le_last T)

lemma totalDegree_singleton (x : IntermediateField K L) : totalDegree (singleton ρ x) = 1 := by
  simp [totalDegree, finrank]
  have : (singleton ρ x).head = (singleton ρ x).last := rfl
  rw [Equality_Degrees this (le_of_eq this)]
  exact Module.finrank_self (singleton ρ x).last

lemma totalDegree_snoc (T : QuadraticTower K L) (F : IntermediateField K L)
    (h : T.last ~[ρ] F) : totalDegree (snoc T F h) = totalDegree T * finrank h.1 := by
  simp [totalDegree, finrank]
  letI : Algebra (T.head) (T.last) := (IntermediateField.inclusion (head_le_last T)).toAlgebra
  letI : Algebra (T.last) F := (IntermediateField.inclusion h.1).toAlgebra
  letI : Algebra (T.head) F := (IntermediateField.inclusion ((le_trans T.head_le_last h.1))).toAlgebra
  have : IsScalarTower T.head T.last F := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  letI : Module (T.head) (T.last) := (IntermediateField.inclusion (head_le_last T)).toAlgebra.toModule
  letI : Module (T.last) F := (IntermediateField.inclusion h.1).toAlgebra.toModule
  letI : Module (T.head) F := (IntermediateField.inclusion ((le_trans T.head_le_last h.1))).toAlgebra.toModule
  have : Module.Free ↥(head T) ↥(T.last) := Module.Free.of_divisionRing _ _
  have : Module.Free ↥(T.last) ↥F := Module.Free.of_divisionRing _ _
  --have : IsScalarTower ↥(head T) ↥(RelSeries.last T) ↥F := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  rw [Module.finrank_mul_finrank, Equality_Degrees, Equality_Degrees']
  · simp
  · simp
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

      sorry
    use QuadraticTower.compose h1 hT2
    simp [QuadraticTower.compose]
    refine ⟨hT₁, ?_⟩
    simp [map_compositum, relHom_comp]
    refine IntermediateField.add_mem (RelSeries.last T₁ ⊔ RelSeries.last T₂) (mem_left_sup hTa ) (mem_right_sup hTb)
  | neg a ha hT =>
    convert hT using 3
    simp
  | mul a b ha hb =>
    sorry
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
      exact deg_le_two_square_root a (RelSeries.last T) hl
    have hr : ∃ h : T.last ≤ F, DegLeTwoExtension h := by use h_le
    use RelSeries.snoc T F hr
    constructor
    · rwa [head_snoc]
    · rw [last_snoc]
      simp [F]
      exact mem_adjoin_simple_self T.last a

lemma miao (L : RelSeries {(x, y) : IntermediateField ℚ ℂ × IntermediateField ℚ ℂ | x ≤ y})
    {i j : Fin (L.length + 1)} (hij : i ≤ j) : L.toFun i ≤  L.toFun j := by
  have := L.rel_or_eq_of_le hij
  simp_all only [ge_iff_le]
  cases this with
  | inl h => simp_all
  | inr h_1 => simp_all

noncomputable def ciccio (L : RelSeries {(x, y) : IntermediateField ℚ ℂ × IntermediateField ℚ ℂ | x ≤ y})
    {i j : Fin (L.length + 1)} (hij : i ≤ j) : Algebra (L.toFun i) (L.toFun j) :=
  (IntermediateField.inclusion (miao L hij)).toAlgebra

noncomputable instance (L : RelSeries {(x, y) : IntermediateField ℚ ℂ × IntermediateField ℚ ℂ | x ≤ y})
    {i : Fin (L.length + 1)} (hi : i < Fin.last L.length) : Algebra (L.toFun i) (L.toFun (i+1)) :=
  (IntermediateField.inclusion (relsucc L hi)).toAlgebra

open QuadraticTower

lemma Tower_Degree_pow_2 (L : QuadraticTower K L) :
      L.totalDegree ∣ 2 ^ L.length := by
  induction L using inductionOn' with
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
