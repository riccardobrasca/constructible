import Mathlib
open Polynomial Real Module IntermediateField IsFractionRing


local notation "θ" => π/9

local notation "β" => (cos θ : ℂ)

local notation "ℚβ" => IntermediateField.adjoin ℚ ({β} : Set ℂ)

-- (what will eventually be) the minimal polynomial of β
local notation "h" => (X ^ 3 - 3 * X - C 1 : Polynomial ℚ)

-- h viewed as a polynomial over ℤ
local notation "h'" => (X ^ 3 - 3 * X - C 1 : Polynomial ℤ)

-- h is the image of h' in Q[x]
lemma h_eq_h' : (map (Int.castRingHom ℚ) h') = h := by
  simp [map_ofNat]

lemma deg_h : (X ^ 3 - 3 * X - C 1 : Polynomial ℚ).natDegree = 3 := by
  compute_degree!

-- h is monic
lemma is_monic_h : Monic h := by
  monicity!

-- h' is monic
lemma is_monic_h' : Monic h' := by
  monicity!

-- beta is a root of h. Only thing left to do!
lemma is_root_beta : (eval₂ (algebraMap ℚ ℂ) β h) = 0 := by
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  sorry

-- alpha is integral over Q
lemma is_integral_beta : IsIntegral ℚ β := by
  use h
  constructor
  · exact is_monic_h
  · exact is_root_beta

-- 1 is not a root of h'
lemma one_not_root : ¬((aeval (1 : ℚ)) h' = 0) := by
  simp [aeval]

-- -1 is not a root of h'
lemma neg_one_not_root : ¬((aeval (-1 : ℚ)) h' = 0) := by
  simp [aeval]
  linarith

-- h' has no roots in Q
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

-- h has no roots in Q
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


-- h is the minimal polynomial of beta
lemma is_min_poly_h : h = minpoly ℚ (↑β : ℂ) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact is_irred_h
  · exact is_root_beta
  · exact is_monic_h

-- [Q(beta):Q] = 3
set_option synthInstance.maxHeartbeats 60000 in
theorem beta_degree : finrank ℚ ℚβ = 3 := by
  rw [adjoin.finrank is_integral_beta, ← is_min_poly_h]
  compute_degree!
