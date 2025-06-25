import Mathlib
import Constructible.alphadegree

/- Inductive Definition of constructible number : constructibles are
 closed under addition, multiplication, inverse, negation, and square root-/

open IntermediateField

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
    Module.finrank K₁ K₃ = Module.finrank K₂ K₃ := by
  subst h
  rfl

lemma Equality_Degrees' {K L : Type*} [Field K]  [Field L] [Algebra L K] {K₁ K₂ K₃ : IntermediateField L K}
    (h : K₂ = K₃) (h1 : K₁ ≤ K₂) :
    letI : Module K₁ K₂ := (IntermediateField.inclusion h1).toAlgebra.toModule
    letI : Module K₁ K₃ := (IntermediateField.inclusion (h ▸ h1)).toAlgebra.toModule
    Module.finrank K₁ K₂ = Module.finrank K₁ K₃ := by
  subst h
  rfl


/- theorem foo (L₁ L₂ : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·))
    (h₁ : ∀ i, (hi : i < Fin.last L₁.length) →
      letI := (IntermediateField.inclusion (ciao L₁ hi)).toAlgebra.toModule
      Module.finrank (L₁.toFun i) (L₁.toFun (i + 1)) ∣ 2)
    (h₂ : ∀ i, (hi : i < Fin.last L₂.length) →
      letI := (IntermediateField.inclusion (ciao L₂ hi)).toAlgebra.toModule
      Module.finrank (L₂.toFun i) (L₂.toFun (i + 1)) ∣ 2)
    (h_le : L₁.last ≤ L₂.head)
    (h12 : letI := (IntermediateField.inclusion h_le).toAlgebra.toModule
      Module.finrank L₁.last L₂.head ∣ 2) :
    L₁.append L₂ := sorry -/


lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔
    ∃ L : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·), x ∈ L.last ∧ L.head = ⊥ ∧
    ∀ i, (hi : i < Fin.last L.length) →
      letI := (IntermediateField.inclusion (ciao L hi)).toAlgebra.toModule
      Module.finrank (L.toFun i) (L.toFun (i + 1)) ∣ 2 := by
    constructor
    · intro h
      induction h with
      | base _ =>
        let L := RelSeries.singleton (α := IntermediateField ℚ ℂ) (· ≤ ·) ⊥
        use L
        simp_all only [RelSeries.last_singleton, eq_ratCast, RelSeries.head_singleton, RelSeries.singleton_length,
          Nat.reduceAdd, Fin.last_zero, Fin.isValue, Fin.not_lt_zero, RelSeries.singleton_toFun, Module.finrank_self,
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
        · let K := (IntermediateField.adjoin L.last {x}).restrictScalars ℚ
          have hK : L.last ≤ K := by
            have := adjoin_contains_field_as_subfield {x} L.last.toSubfield
            simp_all only [AlgHom.toRingHom_eq_coe, coe_toSubfield, coe_type_toSubfield, ge_iff_le, K]
            exact this
          let L' := L.snoc K hK
          use L'
          constructor
          · simp [L', K]
            exact mem_adjoin_simple_self (↥L.last) x
          /- have : Algebra L.last (IntermediateField.adjoin L.last {x}) := by
            sorry -/
          /- have hL' : L.last ≤ (IntermediateField.adjoin L.last {x}) := by
            intro y hy
            --apply IntermediateField.mem_toSubfield

            sorry -/


          --let L' := L.snoc (IntermediateField.adjoin L.last {x})

          · have : L'.head = L.head := by
              aesop
            rw [this]
            refine ⟨h0, ?_⟩
            intro i hi
            simp [L']
            --specialize H' i hi
            sorry
    sorry

noncomputable instance (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
  (i : Fin (L.length + 1)) : Field (L.toFun i) := by
  infer_instance

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

noncomputable instance (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    {i : Fin (L.length + 1)} (hi : i < Fin.last L.length) : Algebra (L.toFun i) (L.toFun (i+1)) :=
  (IntermediateField.inclusion (ciao L hi)).toAlgebra

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
/- Lemma : the degree of a chain of L.Length+1 nested subfields L[i] such that
[L[i]:L[i-1]] = 2 has degree [L[L.Length]:L[0]] = 2^(L.Length)-/
lemma Tower_Degree_pow_2 (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    (H : ∀ i, (hi : i < Fin.last L.length) →
      letI := (IntermediateField.inclusion (ciao L hi)).toAlgebra.toModule
      Module.finrank (L.toFun i) (L.toFun (i+1)) ∣ 2) :
      letI := (IntermediateField.inclusion (RelSeries_head_subset_last L)).toAlgebra
      Module.finrank L.head L.last ∣ 2 ^ L.length := by
    induction L using RelSeries.inductionOn' with
    | singleton x =>
      simp only [RelSeries.singleton_length, pow_zero, Nat.dvd_one]
      exact Module.finrank_self ↥(RelSeries.singleton (fun x1 x2 ↦ x1 ≤ x2) x).head
    | snoc L S hLS h =>
      letI : Algebra L.head L.last := (IntermediateField.inclusion (RelSeries_head_subset_last L)).toAlgebra
      letI : Algebra L.last S := (IntermediateField.inclusion hLS).toAlgebra
      letI : Algebra L.head S := (IntermediateField.inclusion (le_trans (RelSeries_head_subset_last L) hLS)).toAlgebra
      have key : Module.finrank L.last S ∣ 2 := by
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
        ← Module.finrank_mul_finrank L.head L.last S]
      have : (L.snoc S hLS).length = L.length + 1 := by
        aesop
      rw [this, pow_add]
      simp
      apply mul_dvd_mul
      · apply h
        intro i hi
        --specialize H i.castSucc (by simp)
        specialize H i.castSucc (by simp)
        have boh : (i+1).castSucc = i.castSucc + 1 := by
          ext
          simp [Fin.val_add_one]
          aesop
        have := (L.snoc_castSucc S hLS (i+1))
        rw [boh] at this
        rwa [Equality_Degrees (L.snoc_castSucc S hLS i), Equality_Degrees' this] at H

      exact key

lemma rank_eq_pow_two_of_isConstructible' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → Module.finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff] at h
  obtain ⟨ n , f, h1, h2 ⟩ := h
  sorry

lemma rank_eq_pow_two_of_isConstructible'' {x : ℂ} (h : IsConstructible x) :
    ∃ n, x ≠ 0 → Module.finrank ℚ (Submodule.span ℚ {x}) = 2 ^ n := by
  rw[isConstructible_iff] at h
  obtain ⟨L , hL, h0, H⟩ := h
  sorry
  /- have : L ≠ [] := List.ne_nil_of_length_pos hL

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
 -/
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
