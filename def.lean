import Mathlib
open Polynomial
open Module

inductive IsConstructible : ℂ → Prop
  | base (α : ℚ) : IsConstructible (algebraMap ℚ ℂ α)
  | add (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α + β)
  | neg (α : ℂ) : IsConstructible α → IsConstructible (-α)
  | mul (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α * β)
  | inv (α : ℂ) : IsConstructible α → IsConstructible α⁻¹
  | rad (α : ℂ) : IsConstructible (α ^ 2) → IsConstructible α


lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ (n : ℕ), ∃ f : Fin (n+1) → Subfield ℂ,
      ∀ i, ∃ (h : f i ≤ f (i+1)), x ∈ f (Fin.last n) ∧
      letI : Module (f i) (f (i+1)) := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank (f i) (f (i+1)) = 2 := by
  sorry

notation "α" => (2 : ℝ)^((1 : ℝ)/3)

noncomputable def f : Polynomial ℚ := X ^ 3 - C 2

lemma alpha_cube : α ^ 3 = 2 := by
  rw [Real.rpow_pow_comm (by norm_num), ← Real.rpow_natCast_mul (by norm_num)]
  simp

-- alpha is a root of f
lemma is_root_alpha : (eval₂ (algebraMap ℚ ℝ) α f) = 0 := by
  simp only [f, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [alpha_cube]
  simp

--
lemma is_integral_alpha : IsIntegral ℚ α := by
  use f
  constructor
  · rw [Monic.def, f]
    simp [leadingCoeff]
  · exact is_root_alpha

notation "ℚα" => IntermediateField.adjoin ℚ α

lemma alpha_degree : Module.finrank ℚ ℚα =3 := by
  sorry

theorem main : ¬ (IsConstructible ↑α) := by
  intro h
  rw [isConstructible_iff] at h
  obtain ⟨n, f, H⟩ := h
  sorry
