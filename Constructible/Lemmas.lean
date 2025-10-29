import Mathlib

open Fin RelSeries Polynomial IntermediateField SetRel

variable {α : Type*} {r : SetRel α α} (P : {a : α} → {b : α} → a ~[r] b → Prop)

section stuff

--Fin 1 consists of only 0
lemma Fin.eq_zero' {n : ℕ} (hn : n = 0) (i : Fin (n+1)) : i = 0 :=
  (subsingleton_iff_le_one.2 (by omega)).1 _ _

-- a RelSeries with length 0 is a singleton
lemma length_zero {T : RelSeries r} (hT : T.length = 0) : ∃ x, T = singleton r x :=
  ⟨T.head, ext (by simp [hT]) (funext fun i ↦ by simp [eq_zero' hT i, head])⟩

@[simp]
--For some i in Fin (n+1) different from last n, the successior of i as an element of Fin n is i+1
lemma Fin.castPred_succ_eq_add_one {n : ℕ} {i : Fin (n+1)} (hi : i ≠ last n) :
    (i.castPred hi).succ = i + 1 :=
  Fin.ext (by simp [val_add_one, hi])


lemma Fin.snoc_add_one_castPred_of_lt {n : ℕ} {T : Type*} {i : Fin (n+1+1)} (hi : i < last (n+1))
    (hi' : i.castPred hi.ne < last n) (f : Fin (n+1) → T) (x : T) :
    snoc (α := fun _ ↦ T) f x (i+1) = f (i.castPred hi.ne+1) := by
  suffices : i+1 ≠ Fin.last (n+1)
  · rw [← castSucc_castPred _ this, Fin.snoc_castSucc]
    congr
    simp [← val_eq_val, val_add_one_of_lt hi, val_add_one_of_lt hi']
  refine fun h ↦ hi'.ne (castSucc_injective _ ?_)
  simpa [val_add_one_of_lt hi, ← val_eq_val] using h

lemma Fin.snoc_eq_castPred_of_lt {n : ℕ} {T : Type*} {i : Fin (n+1+1)} (hi : i < last (n+1))
    (f : Fin (n+1) → T) (x : T) :
    snoc (α := fun _ ↦ T) f x i = f (i.castPred hi.ne) := by
  conv =>
    enter [1, 3]
    rw [← castSucc_castPred i hi.ne]
  rw [snoc_castSucc]

@[simp]
lemma Fin.snoc_add_one_of_eq_last {n : ℕ} {T : Type*} {i : Fin (n+1+1)} (hi : i < last (n+1))
    (hi' : i.castPred hi.ne = last n) (f : Fin (n+1) → T) (x : T) :
    snoc (α := fun _ ↦ T) f x (i+1) = x := by
  apply_fun castSucc at hi'
  simp at hi'
  simp [hi']

@[simp]
lemma Fin.snoc_eq_of_eq_last {n : ℕ} {T : Type*} {i : Fin (n+1+1)} (hi : i < last (n+1))
    (hi' : i.castPred hi.ne = last n) (f : Fin (n+1) → T) (x : T) :
    snoc (α := fun _ ↦ T) f x i = f (last n) := by
  rw [← castSucc_castPred i hi.ne, Fin.snoc_castSucc, hi']

lemma Fin.tail_eq {n : ℕ} {T : Type*} (i : Fin n) (f : Fin (n + 1) → T) :
    tail (α := fun _ ↦ T) f i = f (i.castSucc + 1) := by
  rw [coeSucc_eq_succ]
  rfl

lemma Fin.init_eq {n : ℕ} {T : Type*} (i : Fin n) (f : Fin (n + 1) → T) : --useless?
    init (α := fun _ ↦ T) f i = f i.castSucc := by
  --rw [eraseLast, coeSucc_eq_succ]
  rfl

lemma relsucc (T : RelSeries r) {i : Fin (T.length + 1)} (hi : i < Fin.last T.length) :
   (T i ~[r] T (i + 1)) := by
  simpa only [← castPred_succ_eq_add_one hi.ne] using T.step (i.castPred hi.ne)

end stuff



variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/- lemma ciao (C : RelSeries {(x, y) : IntermediateField K L × IntermediateField K L | x ≤ y})
    {i : Fin (C.length + 1)} (hi : i < Fin.last C.length) :
    C.toFun i ≤ C.toFun (i+1) := C.rel_of_lt <|Fin.lt_add_one_iff.mpr hi -/

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

open Polynomial IntermediateField Rel

lemma integral (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) : IsIntegral F x := by
  have : ∃ (a : F), x ^ 2 = ↑a := by
    simp
    exact h
  obtain ⟨a, ha⟩ := this
  let f := (X ^ 2 - C a : Polynomial F)
  use f
  have H : (aeval x) f = 0 := by
    simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C,
    IntermediateField.algebraMap_apply, sub_self, f]
  constructor
  · monicity
    simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, sub_self,
      Nat.ofNat_pos, leadingCoeff_X_pow_sub_C, f]
  · exact H

lemma square_min_poly (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) :
    (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 := by
  have : ∃ (a : F), x ^ 2 = (a : L) := by
    simp
    exact h
  obtain ⟨a, ha⟩ := this
  let f := (X ^ 2 - C a : Polynomial F)
  let p := minpoly (↑F) x
  have hf : f ≠ 0 := by
    suffices : natDegree f > 0
    · exact ne_zero_of_natDegree_gt this
    · simp_all only [SetLike.coe_mem, natDegree_sub_C, natDegree_pow,
        natDegree_X, mul_one, gt_iff_lt, Nat.ofNat_pos, f]
  have h_int : IsIntegral F x := by
    exact integral x F h
  have hp : p ≠ 0 := by
    suffices : natDegree p > 0
    · exact ne_zero_of_natDegree_gt this
    · exact minpoly.natDegree_pos (integral x F h)
  have hf_deg : degree f = natDegree f := by exact degree_eq_natDegree hf
  have hf_deg2 : natDegree f = 2 := by
    simp_all only [SetLike.coe_mem, ne_eq, natDegree_sub_C, natDegree_pow,
      natDegree_X, mul_one, Nat.cast_ofNat, f, p]
  rw [hf_deg2] at hf_deg
  have hp_deg : degree p = natDegree p := by exact degree_eq_natDegree hp
  have Hdeg : 0 < p.degree ∧ p.degree ≤ f.degree := by
    constructor
    · rw [hp_deg]
      rw [←gt_iff_lt]
      have : p.natDegree > 0 := by
        exact minpoly.natDegree_pos h_int
      simp_all only [SetLike.coe_mem, ne_eq, Nat.cast_ofNat, natDegree_sub_C,
        natDegree_pow, natDegree_X, mul_one, gt_iff_lt, Nat.cast_pos, p, f]
    · apply minpoly.min
      · monicity
        rw [leadingCoeff_X_pow_sub_C (Nat.le.step Nat.le.refl)]
      · simp_all only [SetLike.coe_mem, map_sub, map_pow, aeval_X, aeval_C,
        IntermediateField.algebraMap_apply, sub_self, f]
  rw [hf_deg] at Hdeg
  have test := Hdeg
  cases' Hdeg : p.degree with n
  · simp_all [p, f]
  · rw [hp_deg] at test
    rw [hp_deg] at Hdeg
    rw [Hdeg] at test
    rw [Hdeg] at hp_deg
    suffices : p.natDegree = 1 ∨ p.natDegree = 2
    · simp_all only [SetLike.coe_mem, ne_eq, Nat.cast_ofNat, natDegree_sub_C,
        natDegree_pow, natDegree_X, mul_one, WithBot.coe_pos, p, f]
    · rcases test with ⟨hn_pos, hn_le⟩
      have hn_pos' : 0 < n := by
        exact WithBot.coe_pos.mp hn_pos
      have hn_le' : n ≤ 2 := by
        exact WithBot.coe_le_coe.mp hn_le
      have testest : p.natDegree = n := by
        exact (degree_eq_iff_natDegree_eq_of_pos hn_pos').mp hp_deg
      interval_cases n
      · left
        exact testest
      · right
        exact testest

-- this should be in mathlib? I couldn't find it anywhere
@[simp]
theorem restrictScalars_extendScalars {K : Type u_1} {L : Type u_2} [Field K] [Field L]
    [Algebra K L] (L' : IntermediateField K L) (E : IntermediateField L' L)
    (h : L' ≤ restrictScalars K E) : extendScalars h = E := by
  rfl

lemma blah (x : L) (F : IntermediateField K L) :
        F ≤ (IntermediateField.adjoin F {x}).restrictScalars K := by
  rw [restrictScalars_adjoin_eq_sup]
  simp
