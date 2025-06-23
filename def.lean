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
      ∀ i, f i ≤ f (i+1) ∧ x ∈ f (Fin.last n) ∧ ∀ i,
      let h : Module (f i) (f (i+1)) := by
        sorry
      Module.finrank (f i) (f (i+1)) = 2 := by
  sorry
