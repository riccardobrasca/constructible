import Mathlib

open Polynomial IntermediateField Module Ideal

-- the cube root of 2
local notation "α" => (2 : ℂ)^((1 : ℂ)/3)

-- α ^ 3 = 2
lemma alpha_cube : α ^ 3 = 2 := by
  simp

--  ℚ(α)
local notation "ℚα" => adjoin ℚ ({↑α} : Set ℂ)

-- (what will eventually be) the minimal polynomial of α
local notation "f" => (X ^ 3 - C 2 : Polynomial ℚ)

-- f viewed as a polynomial over ℤ
local notation "g" => (X ^ 3 - C 2 : Polynomial ℤ)

-- f is the image of g in ℚ[x]
lemma f_eq_g : (map (Int.castRingHom ℚ) g) = f := by
  simp [map_ofNat]

-- f is monic
lemma is_monic_f : Monic f := by
  monicity!

-- g is monic
lemma is_monic_g : Monic g := by
  monicity!

-- α is a root of f
lemma is_root_alpha : (eval₂ (algebraMap ℚ ℂ) α f) = 0 := by
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [alpha_cube]
  simp

-- α is integral over ℚ
lemma is_integral_alpha : IsIntegral ℚ α := by
  use f
  constructor
  · exact is_monic_f
  · exact is_root_alpha

-- the ideal (2) in ℤ
local notation "P" => ((Ideal.span {2}) : Ideal ℤ)

-- the ideal (2) is prime in ℤ
lemma two_is_prime : IsPrime P := by
  refine (span_singleton_prime ?_).mpr ?_
  · norm_num
  · norm_num

-- the leading coefficient of g is not in (2)
lemma one_not_in_ideal : ¬ (leadingCoeff g ∈ P) := by
  have := is_monic_g
  refine Monic.leadingCoeff_notMem this ?_
  refine IsPrime.ne_top ?_
  exact two_is_prime

-- g is irreducible
lemma is_irred_g : Irreducible g := by
  have : degree g = 3 := by
    compute_degree!
  apply irreducible_of_eisenstein_criterion two_is_prime one_not_in_ideal
  · intro n hn
    rw [this] at hn
    simp at hn
    interval_cases n
    · simp
      exact mem_span_singleton_self 2
    · simp
    · simp
  · rw [this]
    norm_num
  · simp
    intro h
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    norm_num at h
  · apply Monic.isPrimitive
    exact is_monic_g

-- f is irreducible
lemma is_irred_f : Irreducible f := by
  rw [← f_eq_g]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast is_monic_g.isPrimitive).1 is_irred_g

-- f is the minimal polynomial of α
lemma is_min_poly_f : f = minpoly ℚ (↑α : ℂ) := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact is_irred_f
  · exact is_root_alpha
  · exact is_monic_f

-- [ℚ(α):ℚ] = 3
set_option synthInstance.maxHeartbeats 60000 in
theorem alpha_degree : finrank ℚ ℚα = 3 := by
  rw [adjoin.finrank is_integral_alpha, ← is_min_poly_f]
  compute_degree!

-- three does not divide any power of two
theorem three_not_dvd_two_pow (n : ℕ) : ¬ (3 ∣ 2 ^ n) := by
  intro hdiv
  simpa using Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv
