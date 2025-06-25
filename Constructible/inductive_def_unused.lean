import Matlib

/-Unused-/

@[elab_as_elim]
lemma IsConstructible.induction (P : ℂ → Prop) {α : ℂ} (hα : IsConstructible α)
    (base : ∀ α : ℚ, P (algebraMap ℚ ℂ α))
    (add : ∀ α β : ℂ, P α → P β → P (α + β))
    (neg : ∀ α : ℂ, P α → P (-α))
    (mul : ∀ α β : ℂ, P α → P β → P (α * β))
    (inv : ∀ α : ℂ, P α → P α⁻¹)
    (rad : ∀ α : ℂ, P (α ^ 2) → P α) :
    P α := by
  revert α
  apply IsConstructible.rec
  · exact base
  · exact fun α β a a a_ih a_ih_2 => add α β a_ih a_ih_2
  · exact fun α a a_ih => neg α a_ih
  · exact fun α β a a a_ih a_ih_2 => mul α β a_ih a_ih_2
  · exact fun α a a_ih => inv α a_ih
  · exact fun α a a_ih => rad α a_ih

lemma rank_eq_pow_two_of_isConstructible {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → Module.finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  induction h with
  | base α =>
    use 0
    intro hα
    simpa using finrank_span_singleton hα
  | add α β _ _ _ _ => sorry
  | neg α _ _ => sorry
  | mul α β _ _ _ _ => sorry
  | inv α _ _ => sorry
  | rad α _ _ => sorry

lemma minpoly_degree_eq_pow_two_of_isConstructible {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → (minpoly ℚ x).natDegree = 2 ^ n := by
  induction h with
  | base α =>
    use 0
    intro hx
    exact minpoly.natDegree_eq_one_iff.mpr <| RingHom.mem_range_self (algebraMap ℚ ℂ) α
  | add α β _ _ _ _ => sorry
  | neg α _ _ => sorry
  | mul α β _ _ _ _ => sorry
  | inv α _ _ => sorry
  | rad α _ _ => sorry
