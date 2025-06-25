import Mathlib
import Constructible.alphadegree

/- Inductive Definition of constructible number : constructibles are
 closed under addition, multiplication, inverse, negation, and square root-/

inductive IsConstructible : ℂ → Prop
  | base (α : ℚ) : IsConstructible (algebraMap ℚ ℂ α)
  | add (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α + β)
  | neg (α : ℂ) : IsConstructible α → IsConstructible (-α)
  | mul (α β : ℂ) : IsConstructible α → IsConstructible β → IsConstructible (α * β)
  | inv (α : ℂ) : IsConstructible α → IsConstructible α⁻¹
  | rad (α : ℂ) : IsConstructible (α ^ 2) → IsConstructible α

/-Equivalent Definition with a chain L of Subfield L[i] having degree
[L[i]:L[i-1]] = 2-/

lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ (n : ℕ), ∃ f : Fin (n+1) → Subfield ℂ, f 0 = ⊥ ∧
      ∀ i, ∃ (h : f i ≤ f (i+1)), x ∈ f (Fin.last n) ∧
      letI : Module (f i) (f (i+1)) := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank (f i) (f (i+1)) = 2 := by
  let L := Submodule.span ℚ {x}
  sorry

lemma isConstructible_iff' (x : ℂ) : IsConstructible x ↔
    ∃ (L : List (Subfield ℂ)), ∃ h : 0 < L.length, L[L.length - 1] = ⊥ ∧ x ∈ L[0] ∧
    (∃ h1 : 1 < L.length, x ∉ L[1]) ∧
    ∀ i, (hi : i < L.length) → ∃ (h : L[i] ≤ L[i-1]),
      letI : Module L[i] L[i-1] := (Subfield.inclusion h).toAlgebra.toModule
      Module.finrank L[i] L[i-1] = 2 := by
  let L := Submodule.span ℚ {x}
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

/- Lemma : the degree of a chain of L.Length+1 nested subfields L[i] such that
[L[i]:L[i-1]] = 2 has degree [L[L.Length]:L[0]] = 2^(L.Length)-/

lemma Tower_Degree_pow_2 (L : RelSeries ((· < ·) : Rel (Subfield ℂ) (Subfield ℂ)))
    (H : ∀ i, (hi : i < Fin.last L.length) →
      letI := (Subfield.inclusion (ciao L hi).le).toAlgebra.toModule
      Module.finrank (L.toFun i) (L.toFun (i+1)) = 2) :
      letI := (Subfield.inclusion (RelSeries_head_subset_last L)).toAlgebra
      Module.finrank L.head L.last = 2 ^ L.length := by
    induction L using RelSeries.inductionOn' with
    | singleton x =>  exact Module.finrank_self _
    | snoc L S hLS h =>
      letI : Algebra L.head L.last := (Subfield.inclusion (RelSeries_head_subset_last L)).toAlgebra
      letI : Algebra L.last S := (Subfield.inclusion hLS.le).toAlgebra
      letI : Algebra L.head S := (Subfield.inclusion (le_trans (RelSeries_head_subset_last L) hLS.le)).toAlgebra
      have key : Module.finrank L.last S = 2 := by
        specialize H (Fin.last _ - 1) (by simp [Fin.sub_one_lt_iff, Fin.last_pos])
        have : (L.snoc S hLS).toFun (Fin.last (L.snoc S hLS).length - 1 + 1) =
          (L.snoc S hLS).toFun (Fin.last (L.snoc S hLS).length) := by simp
        rw [Equality_Degrees' this] at H
        simp_rw [RelSeries.apply_last] at H
        rw [Equality_Degrees' (L.last_snoc S hLS)] at H
        have : (L.snoc S hLS).toFun (Fin.last (L.snoc S hLS).length - 1) = L.last := by
          rw [← L.apply_last, ← L.snoc_cast_castSucc S hLS]
          congr
          ext
          simp [Fin.coe_sub_one]
        rwa [Equality_Degrees this] at H
      have : IsScalarTower L.head L.last S := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
      have : Module.Free L.head L.last := Module.Free.of_divisionRing _ _
      have : Module.Free L.last S := Module.Free.of_divisionRing _ _
      rw [Equality_Degrees (L.head_snoc S hLS), Equality_Degrees' (L.last_snoc S hLS),
        ← Module.finrank_mul_finrank L.head L.last S, h]
      · simp [key, ← pow_succ]
      · intro i hi
        specialize H i.castSucc (by simp)
        have boh : (i+1).castSucc = i.castSucc + 1 := by
          ext
          simp [Fin.val_add_one]
          aesop
        have := (L.snoc_castSucc S hLS (i+1))
        rw [boh] at this
        rwa [Equality_Degrees (L.snoc_castSucc S hLS i), Equality_Degrees' this] at H

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
