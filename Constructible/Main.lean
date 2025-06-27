import Mathlib
import Constructible.alphadegree
import Constructible.Lemmas
import Constructible.QuadraticTower

attribute [local instance 2000] Algebra.toModule Module.toDistribMulAction AddMonoid.toZero
  DistribMulAction.toMulAction MulAction.toSMul
  Ideal.Quotient.commRing CommRing.toRing Ring.toSemiring
  Semiring.toNonUnitalSemiring NonUnitalSemiring.toNonUnitalNonAssocSemiring
  NonUnitalNonAssocSemiring.toAddCommMonoid NonUnitalNonAssocSemiring.toMulZeroClass
  MulZeroClass.toMul Submodule.idemSemiring IdemSemiring.toSemiring CommSemiring.toCommMonoid

/- Inductive Definition of constructible number : constructibles are
 closed under addition, multiplication, inverse, negation, and square root-/

open IntermediateField QuadraticTower

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


/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
lemma RelSeries_head_subset_last (L : RelSeries (α := IntermediateField ℚ ℂ) (· ≤ ·)) : L.head ≤ L.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  rcases L.rel_or_eq_of_le (i := 0) (j := ⟨L.length, by omega⟩) (by simp) with h | h
  · exact h
  · simp [h]
    rfl

lemma isConstructible_iff (x : ℂ) : IsConstructible x ↔ ∃ (T : QuadraticTower ℚ ℂ), T.chain.head = ⊥ ∧
    x ∈ T.chain.last := by
    constructor
    · intro h
      induction h with
      | base x =>
        exact ⟨⟨RelSeries.singleton _ ⊥, by simp⟩, by simp, IntermediateField.algebraMap_mem ⊥ x⟩
      | add x y _ _ _ _ =>
        sorry
      | neg _ _ _ =>
        simp_all only [neg_mem_iff]
      | mul α β _ _ _ _ => sorry
      | inv x _ _ =>
        simp_all only [inv_mem_iff]
      | rad x hx H =>
        obtain ⟨T, hQ, hl⟩ := H
        --obtain ⟨L, hLx2, h0, H'⟩ := H
        by_cases h : x ∈ T.chain.last
        · use T
        · let K := (IntermediateField.adjoin T.chain.last {x}).restrictScalars ℚ
          have hK : T.chain.last ≤ K := by
            have := adjoin_contains_field_as_subfield {x} T.chain.last.toSubfield
            simp_all only [AlgHom.toRingHom_eq_coe, coe_toSubfield, coe_type_toSubfield, ge_iff_le, K]
            exact this
          let K' := singleton K
          have h1 : K = K'.chain.head := by
            sorry
          have hleq : T.chain.last ≤ K'.chain.head := by
            rw [←h1]
            exact hK
          --   have t := adjoin_contains_field_as_subfield {x} T.chain.last.toSubfield
          --   simp_all only [AlgHom.toRingHom_eq_coe, coe_toSubfield, coe_type_toSubfield, ge_iff_le, K]
          --   exa
          --   sorry
          --T.chain.snoc K hK
          let T' := append T K' hleq (help x T.chain.last hl)
          use T'
          constructor
          · convert hQ using 1
            exact head_of_append T K' hleq (help x T.chain.last hl)
          /- have : Algebra L.last (IntermediateField.adjoin L.last {x}) := by
            sorry -/
          /- have hL' : L.last ≤ (IntermediateField.adjoin L.last {x}) := by
            intro y hy
            --apply IntermediateField.mem_toSubfield

            sorry -/


          --let L' := L.snoc (IntermediateField.adjoin L.last {x})

          · suffices : T'.chain.last = K'.chain.last
            · rw [this]
              simp [K', QuadraticTower.singleton, K]
              exact mem_adjoin_simple_self _ x
             --IntermediateField.subset_adjoin T.chain.last ({x})
            · exact last_of_append T K' hleq (help x T.chain.last hl)
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

noncomputable instance (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    {i : Fin (L.length + 1)} (hi : i < Fin.last L.length) : Algebra (L.toFun i) (L.toFun (i+1)) :=
  (IntermediateField.inclusion (ciao L hi)).toAlgebra

set_option maxHeartbeats 0 in
/- set_option synthInstance.maxHeartbeats 0 in
 -//- Lemma : the degree of a chain of L.Length+1 nested subfields L[i] such that
[L[i]:L[i-1]] = 2 has degree [L[L.Length]:L[0]] = 2^(L.Length)-/
lemma Tower_Degree_pow_2 (L : RelSeries ((· ≤ ·) : Rel (IntermediateField ℚ ℂ) (IntermediateField ℚ ℂ)))
    (H : ∀ i, (hi : i < Fin.last L.length) →
      letI := (IntermediateField.inclusion (ciao L hi)).toAlgebra
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


open Module


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

open Module


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
s
theorem cannot_double_cube : ¬(IsConstructible α) := by
  exact degree_three_not_cons α alpha_degree
