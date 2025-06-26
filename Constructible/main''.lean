import Mathlib
import Constructible.alphadegree
open IntermediateField Module

/- Inductive Definition of constructible number : constructibles are
 closed under addition, multiplication, inverse, negation, and square root-/

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
    ∃ n, x ≠ 0 → finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
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



/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
lemma RelSeries_head_subset_last (L : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·)) : L.head ≤ L.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  rcases L.rel_or_eq_of_le (i := 0) (j := ⟨L.length, by omega⟩) (by simp) with h | h
  · exact h
  · simp [h]
    rfl

lemma ciao (L : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·)) {i : Fin (L.length + 1)}
    (hi : i < Fin.last L.length) :
    L.toFun i ≤ L.toFun (i+1) := L.rel_of_lt <|Fin.lt_add_one_iff.mpr hi

/-Trivial Lemma, but requires a proof for Lean-/
lemma Equality_Degrees {K L : Type*} [Field K] [Field L] [Algebra L K] {K₁ K₂ K₃ : IntermediateField L K}
    (h : K₁ = K₂) (h1 : K₁ ≤ K₃) :
    letI : Module K₁ K₃ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module K₂ K₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    finrank K₁ K₃ = finrank K₂ K₃ := by
  subst h
  rfl

lemma Equality_Degrees' {K L : Type*} [Field K]  [Field L] [Algebra L K] {K₁ K₂ K₃ : IntermediateField L K}
    (h : K₂ = K₃) (h1 : K₁ ≤ K₂) :
    letI : Module K₁ K₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module K₁ K₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    finrank K₁ K₂ = finrank K₁ K₃ := by
  subst h
  rfl

lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ L : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·), x ∈ L.last ∧ L.head = ⊥ ∧
    ∀ i, (hi : i < Fin.last L.length) →
      letI := (IntermediateField.inclusion (ciao L hi)).toAlgebra.toModule
      finrank (L.toFun i) (L.toFun (i + 1)) ∣ 2 := by
    constructor
    · intro h
      induction h with
      | base _ =>
        let L := RelSeries.singleton (α := IntermediateField ℚ ℂ) (· ≤ ·) ⊥
        use L
        simp_all only [RelSeries.last_singleton, eq_ratCast, RelSeries.head_singleton, RelSeries.singleton_length,
          Nat.reduceAdd, Fin.last_zero, Fin.isValue, Fin.not_lt_zero, RelSeries.singleton_toFun, finrank_self,
          isUnit_iff_eq_one, IsUnit.dvd, implies_true, and_self, and_true, L]
        apply SubfieldClass.ratCast_mem
      | add x y _ _ _ _ =>
        sorry
      | neg _ _ _ =>
        simp_all only [neg_mem_iff]
      | mul α β _ _ _ _ => sorry
      | inv x _ _ =>
        simp_all only [inv_mem_iff]
      | rad x hx H =>
        obtain ⟨L, hLx2, h0, H'⟩ := H
        by_cases h : x ∈ L.last
        · use L
        · /- have : Algebra L.last (IntermediateField.adjoin L.last {x}).toSubfield := by
            sorry
          have hL' : L.last ≤ (IntermediateField.adjoin L.last {x}).toSubfield := by
            intro y hy
            --apply IntermediateField.mem_toSubfield

            sorry
          let L' := L.snoc (IntermediateField.adjoin L.last {x}).toSubfield -/

          sorry
    sorry

lemma miao (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    {i j : Fin (L.length + 1)} (hij : i ≤ j) : L.toFun i ≤  L.toFun j := by
  have := L.rel_or_eq_of_le hij
  simp_all only [ge_iff_le]
  cases this with
  | inl h => simp_all only
  | inr h_1 => simp_all only [le_refl]

noncomputable def ciccio (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    {i j : Fin (L.length + 1)} (hij : i ≤ j) : Algebra (L.toFun i) (L.toFun j) :=
  (IntermediateField.inclusion (miao L hij)).toAlgebra

--set_option maxHeartbeats 0 in
/- Lemma : the degree of a chain of L.Length+1 nested subfields L[i] such that
[L[i]:L[i-1]] = 2 has degree [L[L.Length]:L[0]] = 2^(L.Length)-/

/- Lemma : the degree of a chain of L.Length+1 nested subfields L[i] such that
[L[i]:L[i-1]] = 2 has degree [L[L.Length]:L[0]] = 2^(L.Length)-/
lemma Tower_Degree_pow_2 (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    (H : ∀ i, (hi : i < Fin.last L.length) →
      letI := (IntermediateField.inclusion (ciao L hi)).toAlgebra.toModule
      finrank (L.toFun i) (L.toFun (i+1)) ∣ 2) :
      letI := (IntermediateField.inclusion (RelSeries_head_subset_last L)).toAlgebra
      finrank L.head L.last ∣ 2 ^ L.length := by
  sorry

lemma rank_eq_pow_two_of_isConstructible' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff] at h
  obtain ⟨ n , f, h1, h2 ⟩ := h
  sorry

lemma rank_eq_pow_two_of_isConstructible'' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff] at h
  obtain ⟨L , hL, h0, H⟩ := h
  sorry


lemma bar {K : Type*} [Field K] [Algebra ℚ K] {F : IntermediateField ℚ K} {x : K}
    (hx : x ∈ F) (hxalg : IsIntegral ℚ x) : (minpoly ℚ x).natDegree ∣ finrank ℚ K := by
  sorry


lemma adjoin_degree_dvd {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] (x : K) :
      finrank F (adjoin F {x}) ∣ finrank F K := by
  rw [← finrank_mul_finrank F (adjoin F {x}) K]
  exact Nat.dvd_mul_right (finrank F (adjoin F {x})) (finrank (adjoin F {x}) K)

instance {F E : Type*} [Field F] [Field E] [Algebra F E] (K : IntermediateField F E) :
    IsScalarTower F (⊥ : IntermediateField F E) K :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

set_option synthInstance.maxHeartbeats 40000 in
lemma rank_bot'' {F E : Type*} [Field F] [Field E] [Algebra F E] (K : IntermediateField F E) :
  Module.rank (⊥ : IntermediateField F E) K = Module.rank F K := by
  rw [← rank_mul_rank F (⊥ : IntermediateField F E) K, IntermediateField.rank_bot, one_mul]

@[simp]
lemma finrank_bot'' {F E : Type*} [Field F] [Field E] [Algebra F E]
  (K : IntermediateField F E) :
  finrank ((⊥ : IntermediateField F E)) ↥K = finrank F ↥K :=
  congr(Cardinal.toNat $(rank_bot'' K))

theorem degree_three_not_cons (x : ℂ) (hx : finrank ℚ (adjoin ℚ {x}) = 3) : ¬(IsConstructible x) := by
  intro h
  have h' := (isConstructible_iff x).mp h
  rcases h' with ⟨a, b, c, d⟩
  refine three_not_dvd_two_pow a.length ?_
  have : finrank ℚ (adjoin ℚ {x}) ∣ finrank ℚ a.last := by
    refine finrank_dvd_of_le_right ?_
    exact adjoin_simple_le_iff.mpr b
  rw [hx, ← finrank_bot'] at this
  refine dvd_trans this ?_
  have H := Tower_Degree_pow_2 a d
  convert H
  rw [Equality_Degrees c]
  simp

-- the cube root of 2
local notation "α" => (2 : ℂ)^((1 : ℂ)/3)

theorem cannot_double_cube : ¬(IsConstructible α) := by
  exact degree_three_not_cons α alpha_degree



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

-- beta is a root of h
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

-- h has no roots in Q
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



example (y : ℚ) : (aeval y) (C 3 : Polynomial ℤ) = 3 := by
  rw [aeval_C]
  simp

lemma h_has_no_rational_roots : ∀ (x : ℚ), ¬((aeval x) h = 0) := by
  intro x hx
  apply h'_has_no_rational_roots x
  rw [← hx]
  simp
  left
  simpa using aeval_natCast x 3


/- note to self
lemma h_has_no_rational_roots : ∀ (x : ℚ), ¬((aeval x) h = 0) := by
  intro x hx
  simp at hx
  have H := h'_has_no_rational_roots
  simp at H
  have : (aeval x) (3 : Polynomial ℤ) = 3 := by
    rw [@map_ofNat]
  apply H x      the aeval is bound in a for all, and so we need to apply H x to transform into a specific x
  rw [this]
  exact hx
-/


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
