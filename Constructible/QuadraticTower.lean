import Mathlib
import Constructible.Lemmas

section test

variable {α : Type*} {r : Rel α α} (P : {a : α} → {b : α} → (r a b) → Prop)

lemma stupid (T : RelSeries r) {i : Fin (T.length + 1)} (hi : i < Fin.last T.length) :
    r (T i) (T (i + 1)) := by
  have := T.step (i.castPred hi.ne)
  convert this
  ext
  simp [Fin.val_add_one, Fin.ne_last_of_lt hi]

def propRel (T : RelSeries r) : Prop :=
  ∀ i, (hi : i < Fin.last T.length) → P (stupid T hi)

open Fin RelSeries

lemma Fin.eq_zero' {n : ℕ} (hn : n = 0) (i : Fin (n+1)) : i = 0 :=
  (subsingleton_iff_le_one.2 (by omega)).1 _ _

lemma length_zero {T : RelSeries r} (hT : T.length = 0) : ∃ x, T = singleton r x :=
  ⟨T.head, ext (by simp [hT]) (funext fun i ↦ by simp [eq_zero' hT i, head])⟩


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
  simp at hi
  set i' := i.castPred hi.ne with hi'def
  simp [RelSeries.append, RelSeries.snoc, append_right_eq_snoc]
  by_cases hi' : i' < Fin.last T.length
  · have := hT i' hi'
    convert this
    · rw [← castSucc_castPred i hi.ne, Fin.snoc_castSucc]
    · suffices : i+1 ≠ Fin.last (T.length + 1)
      · rw [← castSucc_castPred _ this, Fin.snoc_castSucc]
        congr
        simp [← val_eq_val, val_add_one_of_lt hi, val_add_one_of_lt hi', i']
      refine fun h ↦ hi'.ne (castSucc_injective _ ?_)
      simpa [val_add_one_of_lt hi, ← val_eq_val] using h
  · simp at hi'
    convert hP
    · rw [← castSucc_castPred i hi.ne, Fin.snoc_castSucc, ← hi'def, hi', RelSeries.last]
    · apply_fun castSucc at hi'
      simp [i'] at hi'
      simp [hi']

end test

namespace IntermediateField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def DegLeTwoExtension {K L : Type*} [Field K] [Field L] [Algebra K L] {F₁ F₂ : IntermediateField K L}
    (h_le : F₁ ≤ F₂) : Prop :=
  letI := (IntermediateField.inclusion h_le).toAlgebra.toModule
  Module.finrank F₁ F₂ ∣ 2

structure QuadraticTower where
  chain : RelSeries (α := IntermediateField K L) (· ≤ ·)
  quadratic : ∀ i, (hi : i < Fin.last chain.length) → DegLeTwoExtension (ciao chain hi)

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

end QuadraticTower

end IntermediateField
