import Mathlib
import Constructible.alphadegree
open List

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



lemma foo (L : List (Subfield ℂ)) (hL : 0 < L.length) --(hQ : L[L.length - 1] = ⊥)
    (H : ∀ i, (hi : i < L.length) → ∃ (h : L[i] ≤ L[i-1]),
      letI : Module L[i] L[i-1] := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank L[i] L[i-1] = 2) :
      ∃ htop :  L[L.length - 1] ≤ L[0],
      letI : Module L[L.length - 1] L[0] := (Subfield.inclusion htop).toAlgebra.toModule
      Module.finrank L[L.length - 1] L[0] = 2 ^ (L.length - 1) := by
  have : L ≠ [] := List.ne_nil_of_length_pos hL
  induction L, this using List.recNeNil with
  | singleton S => aesop
  | cons S L' hL' h1 =>
    have : 0 < L'.length := by rwa [List.length_pos_iff, ne_eq]
    specialize h1 this
    have : (∀ (i : ℕ) (hi : i < L'.length), ∃ (h : L'[i] ≤ L'[i - 1]),
      letI : Module L'[i] L'[i-1] := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank L'[i] L'[i - 1] = 2) := by

      sorry
    simp

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
  obtain ⟨L , hL, h0, H⟩ := h
  have : L ≠ [] := List.ne_nil_of_length_pos hL

  by_cases hx0 : x = 0
  · use 0
    simp_all
  induction L, this using List.recNeNil generalizing x with
  | singleton S =>
      use 0
      simp_all
  | cons S L' h HL =>
      have : 0 < L'.length := by rwa [List.length_pos_iff, ne_eq]

      specialize HL (x := x) this
      have :  L'[L'.length - 1] = ⊥ := by
        rw [← h0]
        simp
        rw [@List.getElem_length_sub_one_eq_getLast]
        rw [List.getElem_cons_length rfl]
        simp_all
      specialize HL this
      have : x ∈ L'[0] ∧ (∃ h1 : 1 < L'.length, x ∉ L'[1]) ∧ ∀ i, (hi : i < L'.length) → ∃ (h : L'[i] ≤ L'[i-1]),
        letI : Module L'[i] L'[i-1] := (Subfield.inclusion h).toAlgebra.toModule
        Module.finrank L'[i] L'[i-1] = 2 := by
        constructor
        · sorry

        sorry
      specialize HL this
      exact HL

/-   | nil => simp at hL
  | cons head tail ih =>
    by_cases hT : tail = []
    · use 0
      simp_all
      --have := H.1
      exact finrank_span_singleton hx0
    · have hT' : 0 < tail.length := by rwa [List.length_pos_iff, ne_eq]
      specialize ih hT'
    sorry -/



lemma quadratic_tower (L : List (Subfield ℂ)) (hL : 0 < L.length)
    (H : ∀ i, (hi : i < L.length) → ∃ (h : L[i] ≤ L[i-1]),
      letI : Module L[i] L[i-1] := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank L[i] L[i-1] = 2) :
      ∃ htop :  L[L.length - 1] ≤ L[0],
        letI : Module L[L.length - 1] L[0] := (Subfield.inclusion htop).toAlgebra.toModule
        Module.finrank L[L.length - 1] L[0] = 2 ^ (L.length - 1) := by
  sorry

def IsQuadraticTower (n : ℕ) (L : List (Subfield ℂ)) : Prop :=
    L.length = n ∧
    ∀ i, (hi : i < L.length) → ∃ (hi': (L[i] ≤ L[i-1])),
      letI : Module L[i] L[i - 1] := (Subfield.inclusion hi').toAlgebra.toModule
      Module.finrank L[i] L[i - 1] = 2

def BaseIsQ (L : List (Subfield ℂ)) : Prop :=
    L[L.length - 1]! = ℚ

lemma is_module {n : ℕ} {L : List (Subfield ℂ)} (h : IsQuadraticTower n L) :
    Module L[n - 1]! L[0]! := by
  sorry

lemma quadratic_tower_degree {n : ℕ} {L : List (Subfield ℂ)} (h : IsQuadraticTower n L) :
    let M := (L[0]! : Subfield ℂ)
    let R := (L[n - 1]! : Subfield ℂ)
    Module.finrank R M = 2 ^ (n - 1) := by
  sorry








/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
lemma RelSeries_head_subset_last (L : RelSeries (α := Subfield ℂ) (· < ·)) : L.head ≤ L.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  rcases L.rel_or_eq_of_le (i := 0) (j := ⟨L.length, by omega⟩) (by simp) with h | h
  · apply le_of_lt h
  · simp [h]
    rfl

lemma ciao (L : RelSeries (α := Subfield ℂ) (· < ·)) {i : Fin (L.length + 1)} (hi : i < Fin.last L.length) :
    L.toFun i < L.toFun (i+1) := L.rel_of_lt (Fin.lt_add_one_iff.2 hi)

/-Trivial Lemma, but requires a proof for Lean-/
lemma Equality_Degrees {K : Type*} [Field K] {K₁ K₂ K₃ : Subfield K} (h : K₁ = K₂) (h1 : K₁ ≤ K₃) :
    letI : Module K₁ K₃ := (Subfield.inclusion h1).toAlgebra.toModule
    letI : Module K₂ K₃ := (Subfield.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.finrank K₁ K₃ = Module.finrank K₂ K₃ := by
  subst h
  rfl

lemma Equality_Degrees' {K : Type*} [Field K] {K₁ K₂ K₃ : Subfield K} (h : K₂ = K₃) (h1 : K₁ ≤ K₂) :
    letI : Module K₁ K₂ := (Subfield.inclusion h1).toAlgebra.toModule
    letI : Module K₁ K₃ := (Subfield.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.finrank K₁ K₂ = Module.finrank K₁ K₃ := by
  subst h
  rfl

lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ L : RelSeries (α := Subfield ℂ) (· < ·), x ∈ L.last ∧ L.head = ⊥ ∧
    ∀ i, (hi : i < Fin.last L.length) →
      letI := (Subfield.inclusion (ciao L hi).le).toAlgebra.toModule
      Module.finrank (L.toFun i) (L.toFun (i+1)) = 2 := by sorry

-- the cube root of 2
local notation "α" => (2 : ℝ)^((1 : ℝ)/3)

theorem cannot_double_cube : ¬(IsConstructible ↑α) := by
  intro h
  have
  sorry
