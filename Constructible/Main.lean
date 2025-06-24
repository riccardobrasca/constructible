import Mathlib

inductive IsConstructible : ℂ → Prop
  | base (α : ℚ) : IsConstructible (algebraMap ℚ ℂ α)
  | add (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α + β)
  | neg (α : ℂ) : IsConstructible α → IsConstructible (-α)
  | mul (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α * β)
  | inv (α : ℂ) : IsConstructible α → IsConstructible α⁻¹
  | rad (α : ℂ) : IsConstructible (α ^ 2) → IsConstructible α

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

lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ (n : ℕ), ∃ f : Fin (n+1) → Subfield ℂ, f 0 = ⊥ ∧
      ∀ i, ∃ (h : f i ≤ f (i+1)), x ∈ f (Fin.last n) ∧
      letI : Module (f i) (f (i+1)) := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank (f i) (f (i+1)) = 2 := by
  let L := Submodule.span ℚ {x}
  sorry

lemma isConstructible_iff' (x : ℂ) : IsConstructible x ↔
    ∃ (L : List (Subfield ℂ)), ∃ h : 0 < L.length, L[0] = ⊥ ∧
    ∀ i, (hi : i < L.length) → ∃ (h : L[i-1] ≤ L[i]), x ∈ L[i-1] ∧
      letI : Module L[i-1] L[i] := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank L[i-1] L[i] = 2 := by
  let L := Submodule.span ℚ {x}
  sorry

notation "α" => (2 : ℝ)^((1 : ℝ)/3)

lemma alpha_cube : α ^ 3 = 2 := by
  rw [Real.rpow_pow_comm (by norm_num), ← Real.rpow_natCast_mul (by norm_num)]
  simp

theorem main : ¬ (IsConstructible ↑α) := by
  intro h
  rw [isConstructible_iff] at h
  obtain ⟨n, f, H⟩ := h
  sorry


lemma rank_eq_pow_two_of_isConstructible' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → Module.finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff] at h
  obtain ⟨ n , f, h1, h2 ⟩ := h


  induction n with
  | zero =>
    use 0
    simp_all
    intro hx
    specialize h2 0
    rcases h2 with ⟨h3, h4⟩
    aesop
  | succ n hn =>
    let g : Fin (n+1) → Subfield ℂ := fun i ↦ f (Fin.castSucc i )
    specialize hn g
    have : g 0 = ⊥ := by
      rw[← h1]
      rfl
    specialize hn this
    sorry

lemma rank_eq_pow_two_of_isConstructible'' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → Module.finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff'] at h
  obtain ⟨ L , hL, h0, H ⟩ := h
  induction L with
  | nil => simp at hL
  | cons head tail ih =>
      sorry
