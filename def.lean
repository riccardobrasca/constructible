import Mathlib

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

theorem main : ¬ (IsConstructible ↑((2 : ℝ)^((1 : ℝ)/3))) := by
  sorry
