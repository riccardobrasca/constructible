import Mathlib
import Constructible.Lemmas
import Constructible.alphadegree

open Fin RelSeries Polynomial IntermediateField Rel

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def DegLeTwoExtension {F₁ F₂ : IntermediateField K L} (h_le : F₁ ≤ F₂) : Prop :=
  Module.finrank F₁ (extendScalars h_le) ∣ 2

local notation3 "ρ" => {(F₁, F₂) : IntermediateField K L × IntermediateField K L | ∃ h : F₁ ≤ F₂, DegLeTwoExtension h}

lemma help (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (blah x F) := by
  unfold DegLeTwoExtension
  rw [Nat.dvd_prime Nat.prime_two, restrictScalars_extendScalars, adjoin.finrank (integral x F h)]
  exact square_min_poly x F h

variable (K L) in
def QuadraticTower := RelSeries ρ

theorem compositum_le (f : IntermediateField K L) {e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
     f ⊔ e₁ ≤ f ⊔ e₂ := by
  gcongr

noncomputable def IntermediateField.finrank {F₁ F₂ : IntermediateField K L} (h : F₁ ≤ F₂) :=
    letI : Module F₁ F₂ := (IntermediateField.inclusion h).toAlgebra.toModule
    Module.finrank F₁ F₂


set_option maxHeartbeats 0 in --try to make this faster
theorem degree_le {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂)
    (h' : finrank (le_sup_right (b := e₁) (a := f)) ≠ 0) :
    finrank (compositum_le f h) ≤ finrank h := by
  let E₁ := extendScalars (le_refl e₁)
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := e₁) (E := f ⊔ e₁) le_sup_right
  let FE₂ := extendScalars (F := e₁) (E := f ⊔ e₂) (le_trans h le_sup_right)
  have LE1 : FE₁ ≤ FE₂ := by
    rw [IntermediateField.extendScalars_le_extendScalars_iff]
    exact compositum_le f h
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
  assumption
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

namespace QuadraticTower

set_option synthInstance.maxHeartbeats  0 in --try to make this faster
def relHom_comp {F : IntermediateField K L} (h : finrank (OrderBot.bot_le F) ≠ 0) : Rel.Hom ρ ρ where
  toFun x := F ⊔ x
  map_rel' := by
    intro F₁ F₂ h
    obtain ⟨h₁, h₂⟩ := h
    use compositum_le F h₁
    have LE1 : F₁ ≤ F ⊔ F₁ := le_sup_right
    have h₃ : finrank LE1 ≠ 0 := by
      rw [@Nat.ne_zero_iff_zero_lt]
      simp [finrank]
      letI : Module F₁ (F ⊔ F₁ : IntermediateField K L) := (IntermediateField.inclusion LE1).toAlgebra.toModule
      have : Module.Free F₁ (F ⊔ F₁ : IntermediateField K L) := Module.Free.of_divisionRing _ _
      have : Module.Finite ↥F₁ ↥(F ⊔ F₁) := by

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
    simp_all [DegLeTwoExtension]
    convert_to Module.finrank ↥(F ⊔ F₁) ↥(extendScalars (compositum_le F h₁)) ≤ 2 ∧ 0 < Module.finrank ↥(F ⊔ F₁) ↥(extendScalars (compositum_le F h₁))
    · rw [Nat.dvd_prime Nat.prime_two]
      omega
    · constructor
      · sorry
      · apply Nat.pos_of_ne_zero
        sorry


def map_compositum (T : QuadraticTower K L) {F : IntermediateField K L} (h : finrank (OrderBot.bot_le F) ≠ 0) : QuadraticTower K L :=
  T.map (relHom_comp h)

def compose {T₁ T₂ : QuadraticTower K L} (h1 : finrank (OrderBot.bot_le T₁.last) ≠ 0) (h2 : T₂.head = ⊥) :
    QuadraticTower K L := append T₁ (T₂.map_compositum h1) (by
  simp
  constructor
  ·
    sorry
  · sorry)

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
    have h1 := hx.1
    rw [apply_zero, head_snoc, ← apply_zero]
    have h2 : p.toFun (Fin.last p.length) = p.last := rfl
    rw [h2] at hp
    exact le_trans hp h1

noncomputable def totalDegree (T : QuadraticTower K L) : ℕ := finrank (head_le_last T)

lemma totalDegree_singleton (x : IntermediateField K L) : totalDegree (singleton ρ x) = 1 := by
  simp [totalDegree, RelSeries.singleton_length, finrank]
  have : (singleton ρ x).head = (singleton ρ x).last := rfl
  rw [Equality_Degrees this (le_of_eq this)]
  exact Module.finrank_self (singleton ρ x).last

lemma totalDegree_snoc (T : QuadraticTower K L) (F : IntermediateField K L)
    (h : T.last ~[ρ] F) : totalDegree (snoc T F h) = totalDegree T * finrank h.1 := by
  simp [totalDegree, RelSeries.snoc_length, finrank]
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

lemma exists_tower {x : L} (hx : IsConstructible K x) : ∃ (T : QuadraticTower K L), T.head = ⊥ ∧
    x ∈ T.last := by
  induction hx with
  | base a =>
    use RelSeries.singleton _ ⊥
    simpa using IntermediateField.algebraMap_mem ⊥ a
  | add a b ha hb =>
    sorry
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
      exact help a (RelSeries.last T) hl
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
