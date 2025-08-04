import Mathlib
open Polynomial Real Module IntermediateField IsFractionRing

-- the angle which cannot be trisected
local notation "θ₁" => Real.pi / 3

-- θ₁'s non-constructible trisection
local notation "θ₂" => Real.pi / 9

-- the value which cannot be constructed
local notation "β" => (Complex.cos (θ₂ : ℂ))
local notation "γ" => 2 * β

-- this extension will have degree 3 and hence be non-constructible
local notation "ℚγ" => IntermediateField.adjoin ℚ ({γ})

-- (what will eventually be) the minimal polynomial of γ
local notation "h" => (X ^ 3 - 3 * X - C 1 : Polynomial ℚ)

-- h viewed as a polynomial over ℤ
local notation "h'" => (X ^ 3 - 3 * X - C 1 : Polynomial ℤ)

-- h is the image of h' in ℚ[x]
lemma h_eq_h' : (map (Int.castRingHom ℚ) h') = h := by
  simp

-- the degree of h
lemma deg_h : (X ^ 3 - 3 * X - C 1 : Polynomial ℚ).natDegree = 3 := by
  compute_degree!

-- h is monic
lemma is_monic_h : Monic h := by
  monicity!

-- h' is monic
lemma is_monic_h' : Monic h' := by
  monicity!

-- a relation from the triple angle formula for β
lemma beta_relation : 8 * β ^ 3 - 6 * β - 1 = 0 := by
  have rel1 : Complex.cos (3 * θ₂) = 4 * (Complex.cos θ₂) ^ 3 - 3 * (Complex.cos θ₂) := by
    rw [←Complex.cos_three_mul (θ₂)]
  have rel2 : 3 * ((π / 9) : ℂ) = ↑(π / 3) := by
    ring_nf
    simp only [one_div, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [rel2] at rel1
  have rel3 : Complex.cos (↑(π / 3)) = 1 /2 := by
    rw [←Complex.ofReal_cos (π / 3)]
    simp only [cos_pi_div_three, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat]
  rw [rel3] at rel1
  have rel4 : 2 * 1 / 2 = 2 * (4 * Complex.cos (π / 9) ^ 3 - 3 * Complex.cos (π / 9)) := by
    rw [← rel1]
    ring
  simp at rel4
  rw [←Eq.symm rel4]
  ring

-- a relation on γ derived from the above relation on β
lemma gamma_relation : γ ^ 3 - 3 * γ - 1 = 0 := by
  rw [← beta_relation]
  ring

-- γ is a root of h
lemma is_root_gamma : (eval₂ (algebraMap ℚ ℂ) γ h) = 0 := by
  rw [← gamma_relation]
  simp only [map_one, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_ofNat, eval₂_X, eval₂_one]

-- α is integral over ℚ
lemma is_integral_gamma : IsIntegral ℚ γ := by
  use h
  constructor
  · exact is_monic_h
  · exact is_root_gamma

-- 1 is not a root of h'
lemma one_not_root : ¬((aeval (1 : ℚ)) h' = 0) := by
  simp [aeval]

-- -1 is not a root of h'
lemma neg_one_not_root : ¬((aeval (-1 : ℚ)) h' = 0) := by
  simp [aeval]
  linarith

-- h' has no roots in ℚ
lemma h'_has_no_rational_roots : ∀ (x : ℚ), ¬((aeval x) h' = 0) := by
  intro x
  intro H
  obtain ⟨n, hn, hdvd⟩ := exists_integer_of_is_root_of_monic is_monic_h' H
  simp at hdvd
  have hdvd' := isUnit_of_dvd_one hdvd
  have := Int.isUnit_iff.mp hdvd'
  rw [hn] at H
  rw [algebraMap_int_eq] at H
  cases this with
  | inl this1 =>
    rw [this1] at H
    exact one_not_root H
  | inr this2 =>
    rw [this2] at H
    exact neg_one_not_root H

-- h has no roots in ℚ
lemma h_has_no_rational_roots : ∀ (x : ℚ), ¬((aeval x) h = 0) := by
  intro x hx
  apply h'_has_no_rational_roots x
  rw [← hx]
  simp
  left
  simpa using aeval_natCast x 3

-- h is irreducible
lemma is_irred_h : Irreducible h := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [deg_h]
    exact Finset.insert_eq_self.mp rfl
  · exact h_has_no_rational_roots


-- h is the minimal polynomial of β
lemma is_min_poly_h : h = minpoly ℚ (↑γ : ℂ) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact is_irred_h
  · exact is_root_gamma
  · exact is_monic_h

-- [ℚ(β):ℚ] = 3
set_option synthInstance.maxHeartbeats 0 in
theorem gamma_degree : finrank ℚ ℚγ = 3 := by
  rw [adjoin.finrank is_integral_gamma, ← is_min_poly_h]
  compute_degree!
