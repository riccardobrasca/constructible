import Mathlib
import Constructible.Lemmas

open Fin RelSeries

variable {α : Type*} {r : Rel α α} (P : {a : α} → {b : α} → (r a b) → Prop)

section stuff

lemma Fin.eq_zero' {n : ℕ} (hn : n = 0) (i : Fin (n+1)) : i = 0 :=
  (subsingleton_iff_le_one.2 (by omega)).1 _ _

lemma length_zero {T : RelSeries r} (hT : T.length = 0) : ∃ x, T = singleton r x :=
  ⟨T.head, ext (by simp [hT]) (funext fun i ↦ by simp [eq_zero' hT i, head])⟩

@[simp]
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

end stuff

section test

lemma stupid (T : RelSeries r) {i : Fin (T.length + 1)} (hi : i < Fin.last T.length) :
    r (T i) (T (i + 1)) := by
  simpa only [← castPred_succ_eq_add_one hi.ne] using T.step (i.castPred hi.ne)

def propRel (T : RelSeries r) : Prop :=
  ∀ i, (hi : i < Fin.last T.length) → P (stupid T hi)

lemma foo'
    (HP : ∀ (T : RelSeries r) (x : α), propRel P T → (hx : r T.last x)
      → (HP : P hx) → propRel P (T.snoc _ hx)) :
    ∀ (T₁ T₂ : RelSeries r), propRel P T₁ → propRel P T₂ → (connect : r T₁.last T₂.head) →
      (P connect) →
      propRel P (T₁.append T₂ connect) := by
    intro T₁ T₂ h₁ h₂ connect hP
    let x := T₂.head
    by_cases hlen : T₂.length = 0
    · obtain ⟨x, rfl⟩ := length_zero hlen
      exact HP T₁ _ h₁ ‹_› ‹_›
    · let T₂':= T₂.drop ⟨1, by omega⟩
      let T₃ := T₁.append (singleton r x) connect
      have key : T₂'.length < T₂.length := by
        simp [T₂']
        exact Nat.zero_lt_of_ne_zero hlen
      have := foo' ‹_› /- this means "by assumptions" -/ T₃ T₂' sorry sorry sorry (by sorry)
      convert this using 1
      simp [T₂', T₃]
      rw [ RelSeries.append_assoc]
      congr
      simp [x]

      sorry
      simp [x]
      have := T₂.step ⟨0, Nat.zero_lt_of_ne_zero hlen⟩
      aesop

  termination_by T₁ T₂ => T₂.length

lemma miao' (T₁ T₂ : RelSeries r) (h₁ : propRel P T₁) (h₂ : propRel P T₂)
    (connect : r T₁.last T₂.head) (hP : P connect) :
    propRel P (T₁.append T₂ connect) := by
  refine foo' P ?_ T₁ T₂ h₁ h₂ connect hP
  intro T x hT connect hP i hi
  simp [RelSeries.append, RelSeries.snoc, append_right_eq_snoc]
  by_cases hi' : i.castPred hi.ne < Fin.last T.length
  · convert hT _ hi'
    · exact snoc_eq_castPred_of_lt hi T.toFun x
    · exact snoc_add_one_castPred_of_lt hi hi' T.toFun x
  · convert hP
    · exact snoc_eq_of_eq_last hi (by simpa using hi') T.toFun x
    · exact snoc_add_one_of_eq_last hi (by simpa using hi') T.toFun x

end test

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def DegLeTwoExtension {F₁ F₂ : IntermediateField K L}
    (h_le : F₁ ≤ F₂) : Prop :=
  letI := (IntermediateField.inclusion h_le).toAlgebra.toModule
  Module.finrank F₁ F₂ ∣ 2

structure QuadraticTower (K L : Type*) [Field K] [Field L] [Algebra K L] where
  chain : RelSeries (α := IntermediateField K L) (· ≤ ·)
  quadratic : ∀ i, (hi : i < Fin.last chain.length) → DegLeTwoExtension (ciao chain hi)

def compositum (F : IntermediateField K L) :
    ((· ≤ ·) :  IntermediateField K L → IntermediateField K L → Prop) →r
    ((· ≤ ·) :  IntermediateField K L → IntermediateField K L → Prop) where
      toFun := fun K' ↦ F ⊔ K'
      map_rel' := @fun K' K'' h ↦ by
        simp only [sup_le_iff, le_sup_left, true_and]
        apply le_trans h
        exact le_sup_right

theorem leee' (f : IntermediateField K L) {e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
    (compositum f e₁) ≤ (compositum f e₂) := by
  simp [compositum]
  apply le_trans h
  exact le_sup_right

theorem leee (f : IntermediateField K L) {e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
     f ⊔ e₁ ≤ f ⊔ e₂ := by
  gcongr


--set_option maxHeartbeats 0 in
theorem foo {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
    letI := (inclusion (leee f h)).toAlgebra.toModule
    letI := (inclusion h).toAlgebra.toModule
    Module.finrank (f ⊔ e₁ : IntermediateField K L) (f ⊔ e₂ : IntermediateField K L) ≤
    Module.finrank e₁ e₂:= by
  let E₁ := extendScalars (le_refl e₁)
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := e₁) (E := f ⊔ e₁) le_sup_right
  let FE₂ := extendScalars (F := e₁) (E := f ⊔ e₂) (le_trans h le_sup_right)
  have LE1 : FE₁ ≤ FE₂ := by
    rw [IntermediateField.extendScalars_le_extendScalars_iff]
    exact leee f h
  letI := (inclusion LE1).toAlgebra.toModule
  have : FE₂ = FE₁ ⊔ E₂ := by
    rw [IntermediateField.extendScalars_sup]
    simp [FE₂]
    congr 1
    rw [sup_assoc]
    simp_all [sup_of_le_right, FE₂]
  have : Module.finrank FE₁ FE₂ ≤ Module.finrank E₁ E₂ := by
    rw [Equality_Degrees' this]
    have := IntermediateField.finrank_sup_le FE₁ E₂
    letI := (inclusion h).toAlgebra.toModule

    --have a := Module.finrank_mul_finrank e₁ e₂ (f ⊔ e₁ : IntermediateField K L)
    sorry

  assumption
  /- let E₁ := extendScalars (le_refl e₁)
  let E₂ := extendScalars h
  let FE₁ := extendScalars (F := e₁) (E := compositum f e₁) le_sup_right
  let FE₂ := extendScalars (F := e₁) (E := compositum f e₂) (le_trans h le_sup_right)
  have : FE₁ ≤ FE₂ := by
    have := leee f h
    simp_all only [FE₁, FE₂]

    sorry

  have : Module.finrank FE₁ FE₂ ≤ Module.finrank E₁ E₂ := by sorry

  have : FE₂ = FE₁ ⊔ E₂ := by

    sorry
  sorry
 -/

#exit

namespace QuadraticTower

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open RelSeries

def singleton (F : IntermediateField K L) : QuadraticTower K L where
  chain := RelSeries.singleton (· ≤ ·) F
  quadratic := fun i hi => by simp [DegLeTwoExtension]

lemma le_of_lt (T : QuadraticTower K L) {i j : Fin (T.chain.length + 1)} (h : i ≤ j) :
    T.chain.toFun i ≤ T.chain.toFun j := by
  have := T.chain.rel_or_eq_of_le h
  aesop

def append (T₁ T₂ : QuadraticTower K L) (connect_le : T₁.chain.last ≤ T₂.chain.head)
    (connect_rank :  DegLeTwoExtension connect_le) : QuadraticTower K L where
  chain := T₁.chain.append T₂.chain connect_le
  quadratic :=
    miao' _ T₁.chain T₂.chain T₁.quadratic T₂.quadratic connect_le connect_rank

lemma blah (x : ℂ) (F : IntermediateField ℚ ℂ) : F ≤ (IntermediateField.adjoin F {x}).restrictScalars ℚ := by
  sorry

lemma help (x : ℂ) (F : IntermediateField ℚ ℂ) (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (blah x F)  := by
  sorry

lemma head_of_append (T₁ T₂ : QuadraticTower K L) (connect_le : T₁.chain.last ≤ T₂.chain.head)
      (connect_rank :  DegLeTwoExtension connect_le)
      : (append T₁ T₂ connect_le connect_rank).chain.head = T₁.chain.head := by
  sorry

lemma last_of_append (T₁ T₂ : QuadraticTower K L) (connect_le : T₁.chain.last ≤ T₂.chain.head)
      (connect_rank :  DegLeTwoExtension connect_le)
      : (append T₁ T₂ connect_le connect_rank).chain.last = T₂.chain.last := by
  sorry

lemma head_of_append (T₁ T₂ : QuadraticTower K L) (connect_le : T₁.chain.last ≤ T₂.chain.head)
      (connect_rank :  DegLeTwoExtension connect_le)
      : (append T₁ T₂ connect_le connect_rank).chain.head = T₁.chain.head := by
  sorry

lemma last_of_append (T₁ T₂ : QuadraticTower K L) (connect_le : T₁.chain.last ≤ T₂.chain.head)
      (connect_rank :  DegLeTwoExtension connect_le)
      : (append T₁ T₂ connect_le connect_rank).chain.last = T₂.chain.last := by
  sorry

end QuadraticTower

end IntermediateField
