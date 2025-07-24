import Mathlib
import Constructible.Lemmas

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

--this is proved in another file
/- theorem degree_le {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂)
    (h_unneccess? :
    let ha : e₁ ≤ f ⊔ e₁ := le_sup_right
    letI := (inclusion ha).toAlgebra.toModule
    Module.finrank e₁ (f ⊔ e₁ : IntermediateField K L) ≠ 0) :
    letI := (inclusion (compositum_le f h)).toAlgebra.toModule
    letI := (inclusion h).toAlgebra.toModule
    Module.finrank (f ⊔ e₁ : IntermediateField K L) (f ⊔ e₂ : IntermediateField K L) ≤
    Module.finrank e₁ e₂:= by sorry -/

--try:

noncomputable def IntermediateField.finrank {F₁ F₂ : IntermediateField K L} (h : F₁ ≤ F₂) :=
    letI : Module F₁ F₂ := (IntermediateField.inclusion h).toAlgebra.toModule
    Module.finrank F₁ F₂

set_option maxHeartbeats 0 in
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
  have : Module.finrank FE₁ FE₂ ≤ Module.finrank E₁ E₂ := by
    rw [Equality_Degrees' Eq1]
    have key := IntermediateField.finrank_sup_le FE₁ E₂
    letI := (inclusion h).toAlgebra.toModule
    letI := (inclusion LE2).toAlgebra.toModule
    have H_deg : Module.finrank ↥e₁ ↥(FE₁ ⊔ E₂) = Module.finrank ↥e₁ FE₁ * Module.finrank FE₁ ↥(FE₁ ⊔ E₂) := by
      --refine (Module.finrank_mul_finrank ?_ ?_ ?_ ?_ ?_).symm
      have :  Module.Free ↥e₁ ↥FE₁ := by
        exact Module.Free.of_divisionRing ↥e₁ ↥FE₁
      have :  Module.Free ↥FE₁ ↥(FE₁ ⊔ E₂) := by
        exact Module.Free.of_divisionRing ↥FE₁ ↥(FE₁ ⊔ E₂)
      have a := Module.finrank_mul_finrank e₁ FE₁ (FE₁ ⊔ E₂ : IntermediateField e₁ L)
      exact id (Eq.symm a)
    --have a := Module.finrank_mul_finrank e₁ e₂ (f ⊔ e₁ : IntermediateField K L)
    rw [H_deg] at key
    have :  Module.finrank ↥e₁ ↥FE₁ ≠ 0 := by
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

def relHom_comp {F : IntermediateField K L} (h : finrank (OrderBot.bot_le F) ≠ 0) : Rel.Hom ρ ρ where
  toFun x := F ⊔ x
  map_rel' := by
    intro F₁ F₂ h
    obtain ⟨h₁, h₂⟩ := h
    use compositum_le F h₁
    have LE1 : F₁ ≤ F ⊔ F₁ := le_sup_right
    have h₃ : finrank LE1 ≠ 0 := by

      sorry
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
