import Mathlib
open Polynomial IntermediateField Module Ideal


-- the cube root of 2
notation "α" => (2 : ℝ)^((1 : ℝ)/3)

-- alpha cubes to 2
lemma alpha_cube : α ^ 3 = 2 := by
  rw [Real.rpow_pow_comm (by norm_num), ← Real.rpow_natCast_mul (by norm_num)]
  simp

-- Q adjoin the cube root of 2
notation "ℚα" => IntermediateField.adjoin ℚ {↑α}

-- (what will eventually be) the minimal polynomial of alpha
notation "f" => (X ^ 3 - C 2 : Polynomial ℚ)

notation "g" => (X ^ 3 - C 2 : Polynomial ℤ)

-- f is the image of g in Q[x]
lemma f_eq_g : (map (Int.castRingHom ℚ) g) = f := by
  simp [map_ofNat]

-- f is monic
lemma is_monic_f : Monic f := by
  monicity!

-- g is monic
lemma is_monic_g : Monic g := by
  monicity!

-- the ideal (2) in Z
notation "P" => ((Ideal.span {2}) : Ideal ℤ)

-- the ideal (2) is prime in Z
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

-- alpha is a root of f
lemma is_root_alpha : (eval₂ (algebraMap ℚ ℝ) α f) = 0 := by
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [alpha_cube]
  simp

-- alpha is integral over Q
lemma is_integral_alpha : IsIntegral ℚ α := by
  use f
  constructor
  · exact is_monic_f
  · exact is_root_alpha

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

-- f is the minimal polynomial of alpha
lemma is_min_poly_f : f = minpoly ℚ α := by
  apply minpoly.eq_of_irreducible_of_monic
  · exact is_irred_f
  · exact is_root_alpha
  · exact is_monic_f

-- [Q(alpha):Q] = 3
theorem alpha_degree : finrank ℚ ℚα = 3 := by
  rw [adjoin.finrank is_integral_alpha, ← is_min_poly_f]
  compute_degree!
