import Mathlib
import Constructible.Lemmas

open Fin RelSeries Polynomial IntermediateField Rel SetRel

variable {α : Type*} {r : SetRel α α} (P : {a : α} → {b : α} → a ~[r] b → Prop)

section propRel



def propRel (T : RelSeries r) : Prop :=
  ∀ i, (hi : i < Fin.last T.length) → P (relsucc T hi)

lemma propRel_tail {T : RelSeries r} (hl : T.length ≠ 0) (hT : propRel P T) :
    propRel P (T.tail hl) := by
  intro i hi
  simp_all [tail_length]
  let i' : Fin (T.length + 1) := ⟨i.1 + 1, by
    simp_all
    omega⟩
  have hi' : i' < Fin.last T.length := by
    simp_all only [tail_length, i']
    refine mk_lt_of_lt_val ?_
    simp_all only [val_last]
    exact Nat.add_lt_of_lt_sub hi
  convert hT i' hi'
  rw [Fin.tail_eq]
  congr
  ext
  exact val_add_one_of_lt hi

lemma propRel_eraseLast {T : RelSeries r} /- (hl : T.length ≠ 0)  -/(hT : propRel P T) :
    propRel P T.eraseLast := by
  intro i hi
  simp_all [eraseLast_length]
  let i' : Fin (T.length + 1) := ⟨i.1, by
    simp_all
    omega⟩
  have hi' : i' < Fin.last T.length := by
    simp_all [eraseLast_length, i']
    refine mk_lt_of_lt_val ?_
    simp_all  [val_last]
    exact Nat.lt_of_lt_pred hi
  convert hT i' hi' using 2
  ext
  rw [val_add_one_of_lt hi, val_add_one_of_lt hi']

lemma propRel_append_aux
    (HP : ∀ (T : RelSeries r) (x : α), propRel P T → (hx : T.last ~[r] x)
      → (HP : P hx) → propRel P (T.snoc _ hx)) :
    ∀ (T₁ T₂ : RelSeries r), propRel P T₁ → propRel P T₂ → (connect : T₁.last ~[r] T₂.head) →
      (P connect) →
      propRel P (T₁.append T₂ connect) := by
    intro T₁ T₂ h₁ h₂ connect hP
    by_cases hlen : T₂.length = 0
    · obtain ⟨_, rfl⟩ := length_zero hlen
      exact HP T₁ _ h₁ ‹_› ‹_›
    · let x := T₂.head
      let T₂':= T₂.tail hlen
      let T₃ := T₁.append (singleton r x) connect
      have key : T₂'.length < T₂.length := by
        simpa [T₂'] using Nat.zero_lt_of_ne_zero hlen
      have h2 : T₃.last ~[r] T₂'.head := by
        simp only [T₃, T₂']
        rw [@last_append]
        simp [x]
        rw [head]
        have : 0 < Fin.last T₂.length := by aesop
        have := relsucc T₂ (i := 0) this
        simp_all
      have h3 : P h2 := by
        have := h₂ 0 (by aesop)
        simp_all  [last_append, last_singleton, head_tail, T₃, x, T₂']
      have := propRel_append_aux ‹_› /- this means "by assumption" -/ T₃ T₂' (HP T₁ x h₁ connect hP)
        (propRel_tail P hlen h₂) h2 h3
      convert this using 1
      simp only [T₃, T₂']
      have := T₂.step ⟨0, Nat.zero_lt_of_ne_zero hlen⟩
      rw [RelSeries.append_assoc _ _ _ _ this]
      simp [x, RelSeries.cons_self_tail]

  termination_by _ T₂ => T₂.length

lemma PropRel_append (T₁ T₂ : RelSeries r) (h₁ : propRel P T₁) (h₂ : propRel P T₂)
    (connect : T₁.last ~[r] T₂.head) (hP : P connect) :
    propRel P (T₁.append T₂ connect) := by
  refine propRel_append_aux P ?_ T₁ T₂ h₁ h₂ connect hP
  intro T x hT connect hP i hi
  simp [RelSeries.append, RelSeries.snoc, append_right_eq_snoc]
  by_cases hi' : i.castPred hi.ne < Fin.last T.length
  · convert hT _ hi'
    · exact snoc_eq_castPred_of_lt hi T.toFun x
    · exact snoc_add_one_castPred_of_lt hi hi' T.toFun x
  · convert hP
    · exact snoc_eq_of_eq_last hi (by simpa using hi') T.toFun x
    · exact snoc_add_one_of_eq_last hi (by simpa using hi') T.toFun x

end propRel

variable {K L : Type*} [Field K] [Field L] [Algebra K L]


/-
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
  exact le_sup_right -/



theorem leee (f : IntermediateField K L) {e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂) :
     f ⊔ e₁ ≤ f ⊔ e₂ := by
  gcongr

--set_option maxHeartbeats 0 in
theorem degree_le {f e₁ e₂ : IntermediateField K L} (h : e₁ ≤ e₂)
    (h_unneccess? :
    let ha : e₁ ≤ f ⊔ e₁ := le_sup_right
    letI := (inclusion ha).toAlgebra.toModule
    Module.finrank e₁ (f ⊔ e₁ : IntermediateField K L) ≠ 0) :
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
  have Eq1 : FE₂ = FE₁ ⊔ E₂ := by
    rw [IntermediateField.extendScalars_sup]
    simp [FE₂]
    congr 1
    rw [sup_assoc]
    simp_all [sup_of_le_right]
  have LE2 : FE₁ ≤ FE₁ ⊔ E₂ := le_trans LE1 <| le_of_eq Eq1
  have : Module.finrank FE₁ FE₂ ≤ Module.finrank E₁ E₂ := by
    rw [Equality_Degrees' Eq1]
    have key := IntermediateField.finrank_sup_le FE₁ E₂
    letI := (inclusion h).toAlgebra.toModule
    let I := (inclusion  LE2).toAlgebra.toModule
    have H_deg : Module.finrank ↥e₁ ↥(FE₁ ⊔ E₂) = Module.finrank ↥e₁ FE₁ * Module.finrank FE₁ ↥(FE₁ ⊔ E₂) := by
      --refine (Module.finrank_mul_finrank ?_ ?_ ?_ ?_ ?_).symm
      have :  Module.Free ↥e₁ ↥FE₁ := by
        exact Module.Free.of_divisionRing ↥e₁ ↥FE₁
      have :  Module.Free ↥FE₁ ↥(FE₁ ⊔ E₂) := by
        exact Module.Free.of_divisionRing ↥FE₁ ↥(FE₁ ⊔ E₂)
      have a := Module.finrank_mul_finrank e₁ FE₁ (FE₁ ⊔ E₂ : IntermediateField e₁ L)
      exact id (Eq.symm a)
    --have a := Module.finrank_mul_finrank e₁ e₂ (f ⊔ e₁ : IntermediateField K L)
    rw [H_deg] at key
    have : Module.finrank ↥e₁ ↥FE₁ ≠ 0 := h_unneccess?
    rw [mul_le_mul_iff_right₀ (pos_of_ne_zero this)] at key
    exact key
  assumption



def DegLeTwoExtension {F₁ F₂ : IntermediateField K L}
    (h_le : F₁ ≤ F₂) : Prop :=
  Module.finrank F₁ (extendScalars h_le) ∣ 2

structure QuadraticTower (K L : Type*) [Field K] [Field L] [Algebra K L] where
  chain : RelSeries {(x, y) : IntermediateField K L × IntermediateField K L | x ≤ y}
  quadratic : ∀ i, (hi : i < Fin.last chain.length) → DegLeTwoExtension (relsucc chain hi)

/-
theorem quadratic_tower_eq {T₁ T₂ : QuadraticTower K L} (h : T₁.chain = T₂.chain) : T₁ = T₂ := by
  cases T₁
  cases T₂
  congr -/

namespace QuadraticTower

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open RelSeries

instance : CoeFun (QuadraticTower K L) (fun x ↦ Fin (x.chain.length + 1) → IntermediateField K L) :=
{ coe f :=  f.chain.toFun }


def singleton (F : IntermediateField K L) : QuadraticTower K L where
  chain := RelSeries.singleton {(x, y) : IntermediateField K L × IntermediateField K L | x ≤ y} F
  quadratic := fun i hi => by simp [DegLeTwoExtension]

instance : Inhabited (QuadraticTower K L) where
  default := singleton (⊥ : IntermediateField K L)

instance : Nonempty (QuadraticTower K L) := instNonemptyOfInhabited

set_option backward.dsimp.proofs true in
@[ext (iff := false)]
lemma ext {x y : QuadraticTower K L} (length_eq : x.chain.length = y.chain.length)
    (toFun_eq : x.chain.toFun = y.chain.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨⟨x1, x2⟩, x_quadratic⟩
  dsimp only at length_eq toFun_eq
  subst length_eq toFun_eq
  rfl

lemma le_of_le (T : QuadraticTower K L) {i j : Fin (T.chain.length + 1)} (h : i ≤ j) :
    T.chain.toFun i ≤ T.chain.toFun j := by
  have := T.chain.rel_or_eq_of_le h
  aesop

instance membership : Membership (IntermediateField K L) (QuadraticTower K L) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩

variable {T : QuadraticTower K L} {x : IntermediateField K L}

theorem mem_def : x ∈ T ↔ x ∈ Set.range T := Iff.rfl

theorem subsingleton_of_length_eq_zero (hs : T.chain.length = 0) : {x | x ∈ T}.Subsingleton := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
  exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _

def head (T : QuadraticTower K L) : IntermediateField K L := T 0

lemma head_chain (T : QuadraticTower K L) :
    T.head = T.chain.head := rfl

def last (T : QuadraticTower K L) : IntermediateField K L  := T <| Fin.last _

def eraseLast (T : QuadraticTower K L) : QuadraticTower K L where
  chain := T.chain.eraseLast
  quadratic := fun i hi => propRel_eraseLast _ T.quadratic i hi

lemma apply_zero (T : QuadraticTower K L) : T 0 = T.head := rfl

lemma apply_last (T : QuadraticTower K L) : T (Fin.last <| T.chain.length) = T.last := rfl

lemma head_mem (T : QuadraticTower K L) : T.head ∈ T := ⟨_, rfl⟩

lemma last_mem (T : QuadraticTower K L) : T.last ∈ T := ⟨_, rfl⟩

@[simp]
lemma head_singleton (x : IntermediateField K L) : (singleton x).head = x := by simp [singleton, head]

@[simp]
lemma last_singleton (x : IntermediateField K L) : (singleton x).last = x := by simp [singleton, last]

def append (T₁ T₂ : QuadraticTower K L) {connect_le : T₁.chain.last ≤ T₂.chain.head}
    (connect_rank : DegLeTwoExtension connect_le) : QuadraticTower K L where
  chain := T₁.chain.append T₂.chain connect_le
  quadratic :=
    PropRel_append _ T₁.chain T₂.chain T₁.quadratic T₂.quadratic connect_le connect_rank

def snoc (T : QuadraticTower K L) (x : IntermediateField K L)
    (hx : T.chain.last ≤ x) (hx2 : DegLeTwoExtension hx) : QuadraticTower K L :=
  T.append (singleton x) hx2

/-Lemma stating that the first subfield L[0] of a chain of nested subfields L is a
subfield of the last subfield L[L.length] in the chain-/
lemma head_le_last (T : QuadraticTower K L) :
    T.chain.head ≤ T.chain.last := by
  rw [← RelSeries.apply_zero, ← RelSeries.apply_last]
  rcases T.chain.rel_or_eq_of_le (i := 0) (j := ⟨T.chain.length, by omega⟩) (by simp) with h | h
  · exact h
  · simp [h]
    rfl

noncomputable def totalDegree (T : QuadraticTower K L) : ℕ :=
  letI := (IntermediateField.inclusion (head_le_last T)).toAlgebra.toModule
  Module.finrank T.chain.head T.chain.last

@[elab_as_elim]
def inductionOn' (motive : QuadraticTower K L → Sort*)
    (singleton : (x : IntermediateField K L) → motive (singleton x))
    (snoc : (T : QuadraticTower K L) → (x : IntermediateField K L) → (hx : T.chain.last ≤ x) → (hx' : DegLeTwoExtension hx) → (hp : motive T) →
      motive (T.snoc x hx hx')) (T : QuadraticTower K L) :
    motive T := by
  let this {n : ℕ} (heq : T.chain.length = n) : motive T := by
    induction n generalizing T with
    | zero =>
      convert singleton T.chain.head
      obtain ⟨x, hx⟩ := length_zero heq
      simp only [hx, RelSeries.head_singleton]
      ext n k
      · exact heq
      · simp [show n = 0 by omega, apply_zero]
        have : T.head = x := by
          rw [head_chain, hx]
          rfl
        rw [this]
    | succ d hd =>
      have ne0 : T.chain.length ≠ 0 := by simp [heq]
      have len : T.chain.eraseLast.length = d := by simp [heq]
      have hle : T.eraseLast.chain.last ≤ T.last := by

        sorry
      have hx' : DegLeTwoExtension hle := by

        sorry
      have hp : motive T.eraseLast :=  hd T.eraseLast len
      convert snoc T.eraseLast T.last hle hx' hp


      --convert snoc
      /- convert snoc T.chain.eraseLast T.chain.last (T.chain.eraseLast_last_rel_last ne0)
        (hd _ len) -/
      --exact (p.snoc_self_eraseLast ne0).symm
      sorry
  exact this rfl

lemma help (x : L) (F : IntermediateField K L) (h : x ^ 2 ∈ F) :
    DegLeTwoExtension (blah x F) := by
  unfold DegLeTwoExtension
  rw [Nat.dvd_prime Nat.prime_two, restrictScalars_extendScalars, adjoin.finrank (integral x F h)]
  exact square_min_poly x F h

end QuadraticTower
