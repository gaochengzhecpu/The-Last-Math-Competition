import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false

namespace Conjecture6322
open scoped BigOperators
open Function

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]

def sign (b : Bool) : R := if b then -1 else 1

@[simp] theorem sign_not (b : Bool) : sign (R := R) (!b) = -sign b := by
  cases b <;> simp [sign]

@[simp] theorem sign_square (b : Bool) : sign (R := R) b * sign b = 1 := by
  cases b <;> simp [sign]

def weight (δ : ι → Bool) : R := ∏ i, sign (δ i)

omit [DecidableEq ι] in
theorem weight_square (δ : ι → Bool) : weight (R := R) δ * weight δ = 1 := by
  unfold weight
  rw [← Finset.prod_mul_distrib]
  simp

def flipAt (i : ι) (δ : ι → Bool) : ι → Bool := Function.update δ i (!δ i)

omit [Fintype ι] in
theorem flipAt_involutive (i : ι) : Function.Involutive (flipAt i) := by
  intro δ
  ext j
  by_cases h : j = i <;> simp [flipAt, Function.update_apply, h]

theorem weight_flip (i : ι) (δ : ι → Bool) :
    weight (R := R) (flipAt i δ) = -weight δ := by
  unfold weight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hp : (∏ j : {j // j ≠ i}, sign (R := R) (flipAt i δ j.1)) =
      ∏ j : {j // j ≠ i}, sign (δ j.1) := by
    apply Finset.prod_congr rfl
    intro j _
    simp [flipAt, Function.update_of_ne j.2]
  rw [hp, Fintype.prod_eq_mul_prod_subtype_ne (fun j => sign (R := R) (δ j)) i]
  simp [flipAt]

def coefficient (f : ι → ι) (δ : ι → Bool) : R :=
  weight δ * ∏ j, sign (δ (f j))

omit [DecidableEq ι] in
theorem coefficient_bijective (f : ι → ι) (hf : Function.Bijective f) (δ : ι → Bool) :
    coefficient (R := R) f δ = 1 := by
  have hp : (∏ j, sign (R := R) (δ (f j))) = weight δ :=
    hf.prod_comp (fun j => sign (δ j))
  rw [coefficient, hp, weight_square]

theorem coefficient_flip (f : ι → ι) (i : ι) (hi : ∀ j, f j ≠ i) (δ : ι → Bool) :
    coefficient (R := R) f (flipAt i δ) = -coefficient f δ := by
  have hp : (∏ j, sign (R := R) (flipAt i δ (f j))) = ∏ j, sign (δ (f j)) := by
    apply Finset.prod_congr rfl
    intro j _
    simp [flipAt, Function.update_of_ne (hi j)]
  rw [coefficient, weight_flip, hp, coefficient, neg_mul]

theorem eq_zero_of_eq_neg [NeZero (2 : R)] (x : R) (hx : x = -x) : x = 0 := by
  have h : (2 : R) * x = 0 := by
    calc
      2 * x = x + x := two_mul x
      _ = x + -x := congrArg (x + ·) hx
      _ = 0 := add_neg_cancel x
  exact (mul_eq_zero.mp h).resolve_left (NeZero.ne (2 : R))

theorem coefficient_sum [NeZero (2 : R)] (f : ι → ι) :
    (∑ δ : ι → Bool, coefficient (R := R) f δ) =
      if Function.Bijective f then (2 : R) ^ Fintype.card ι else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [if_pos hf]
    simp [coefficient_bijective f hf, Fintype.card_fun]
  · rw [if_neg hf]
    have hn : ¬ Function.Surjective f := by
      intro hs
      exact hf ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
    simp only [Function.Surjective, not_forall, not_exists] at hn
    obtain ⟨i, hi⟩ := hn
    have hs := (flipAt_involutive i).bijective.sum_comp
      (fun δ : ι → Bool => coefficient (R := R) f δ)
    simp_rw [coefficient_flip f i hi, Finset.sum_neg_distrib] at hs
    exact eq_zero_of_eq_neg _ hs.symm

def term (A : Matrix ι ι R) (δ : ι → Bool) : R :=
  weight δ * ∏ j, ∑ i, sign (δ i) * A i j

theorem term_expansion (A : Matrix ι ι R) (δ : ι → Bool) :
    term A δ = ∑ f : ι → ι, coefficient f δ * ∏ j, A (f j) j := by
  unfold term
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Finset.prod_mul_distrib, coefficient]
  ring

def bijectionsEquivPerm : {f : ι → ι // Function.Bijective f} ≃ Equiv.Perm ι where
  toFun f := Equiv.ofBijective f.1 f.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv _ := rfl
  right_inv σ := by ext i; rfl

theorem sum_bijective_functions (p : (ι → ι) → R) :
    (∑ f : ι → ι, if Function.Bijective f then p f else 0) =
      ∑ σ : Equiv.Perm ι, p σ := by
  classical
  calc
    _ = ∑ f ∈ Finset.univ.filter Function.Bijective, p f :=
      (Finset.sum_filter _ _).symm
    _ = ∑ f : {f : ι → ι // Function.Bijective f}, p f.1 :=
      Finset.sum_subtype _ (by simp) p
    _ = _ := bijectionsEquivPerm.sum_comp (fun σ => p σ)

/-- The full Boolean-cube identity uses the actual Mathlib permanent. -/
theorem full_formula [NeZero (2 : R)] (A : Matrix ι ι R) :
    (∑ δ : ι → Bool, term A δ) = (2 : R) ^ Fintype.card ι * A.permanent := by
  classical
  calc
    _ = ∑ f : ι → ι, (∑ δ : ι → Bool, coefficient (R := R) f δ) *
        ∏ j, A (f j) j := by
      simp_rw [term_expansion]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      rw [Finset.sum_mul]
    _ = _ := by
      simp_rw [coefficient_sum, ite_mul, zero_mul]
      rw [sum_bijective_functions, ← Finset.mul_sum]
      rfl

def opposite (δ : ι → Bool) : ι → Bool := fun i => !δ i

omit [Fintype ι] [DecidableEq ι] in
theorem opposite_involutive : Function.Involutive (opposite (ι := ι)) := by
  intro δ
  funext i
  simp [opposite]

omit [Fintype ι] [DecidableEq ι] in
theorem opposite_ne_self (i : ι) (δ : ι → Bool) : opposite δ ≠ δ := by
  intro h
  have hi := congrFun h i
  cases hb : δ i <;> simp [opposite, hb] at hi

omit [DecidableEq ι] in
theorem term_opposite (A : Matrix ι ι R) (δ : ι → Bool) :
    term A (opposite δ) = term A δ := by
  unfold term weight opposite
  simp_rw [sign_not, neg_mul, Finset.sum_neg_distrib]
  rw [Finset.prod_neg, Finset.prod_neg, mul_mul_mul_comm, ← mul_pow]
  simp

def positive (i : ι) : Finset (ι → Bool) := Finset.univ.filter (fun δ => δ i = false)

def negative (i : ι) : Finset (ι → Bool) := Finset.univ.filter (fun δ => δ i ≠ false)

theorem half_sums_equal (A : Matrix ι ι R) (i : ι) :
    (∑ δ ∈ positive i, term A δ) = ∑ δ ∈ negative i, term A δ := by
  apply Finset.sum_bij (fun δ _ => opposite δ)
  · intro δ hδ
    have h : δ i = false := (Finset.mem_filter.mp hδ).2
    simp [negative, opposite, h]
  · intro δ _ ε _ h
    exact opposite_involutive.injective h
  · intro δ hδ
    have h : δ i ≠ false := (Finset.mem_filter.mp hδ).2
    refine ⟨opposite δ, ?_, opposite_involutive δ⟩
    cases hb : δ i <;> simp_all [positive, opposite]
  · intro δ _
    exact (term_opposite A δ).symm

theorem pairing_identity (A : Matrix ι ι R) (i : ι) :
    (∑ δ : ι → Bool, term A δ) = 2 * ∑ δ ∈ positive i, term A δ := by
  have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun δ : ι → Bool => δ i = false)
    (term A)
  change (∑ δ ∈ positive i, term A δ) + (∑ δ ∈ negative i, term A δ) = _ at h
  rw [← half_sums_equal A i] at h
  rw [two_mul]
  exact h.symm

theorem number_of_terms (i : ι) : (positive i).card = 2 ^ (Fintype.card ι - 1) := by
  simpa [positive] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset Bool) i
      (Finset.mem_univ false)

theorem sign_injective [NeZero (2 : R)] : Function.Injective (sign (R := R)) := by
  intro b c h
  cases b <;> cases c
  · rfl
  · have he : (1 : R) = 0 := eq_zero_of_eq_neg 1 (by simpa [sign] using h)
    exact False.elim (one_ne_zero he)
  · have he : (1 : R) = 0 := eq_zero_of_eq_neg 1 (by simpa [sign] using h.symm)
    exact False.elim (one_ne_zero he)
  · rfl

theorem reduced_formula [NeZero (2 : R)] (A : Matrix ι ι R) (i : ι) :
    (∑ δ ∈ positive i, term A δ) = (2 : R) ^ (Fintype.card ι - 1) * A.permanent := by
  have hp : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hpow : (2 : R) ^ Fintype.card ι = 2 * (2 : R) ^ (Fintype.card ι - 1) := by
    calc
      _ = (2 : R) ^ ((Fintype.card ι - 1) + 1) :=
        congrArg (fun n => (2 : R) ^ n) (Nat.sub_add_cancel hp).symm
      _ = _ := by rw [pow_succ, mul_comm]
  apply mul_left_cancel₀ (NeZero.ne (2 : R))
  rw [← pairing_identity A i, full_formula, hpow]
  ring

theorem glynn_formula [NeZero (2 : R)] (A : Matrix ι ι R) (i : ι) :
    A.permanent = (∑ δ ∈ positive i, term A δ) / (2 : R) ^ (Fintype.card ι - 1) := by
  apply (eq_div_iff (pow_ne_zero _ (NeZero.ne (2 : R)))).mpr
  rw [reduced_formula]
  exact mul_comm _ _

/-- Exact free pairing, exact term count, and exact conversion constant. -/
theorem pairing_reduction [NeZero (2 : R)] (A : Matrix ι ι R) (i : ι) :
    (∀ δ : ι → Bool, opposite δ ≠ δ ∧ term A (opposite δ) = term A δ) ∧
    ((∑ δ : ι → Bool, term A δ) = 2 * ∑ δ ∈ positive i, term A δ) ∧
    (positive i).card = 2 ^ (Fintype.card ι - 1) ∧
    A.permanent = (∑ δ ∈ positive i, term A δ) / (2 : R) ^ (Fintype.card ι - 1) := by
  exact ⟨fun δ => ⟨opposite_ne_self i δ, term_opposite A δ⟩,
    pairing_identity A i, number_of_terms i, glynn_formula A i⟩

theorem glynn_succ [NeZero (2 : R)] (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = (∑ δ ∈ positive 0, term A δ) / (2 : R) ^ n := by
  simpa using glynn_formula A 0

end Conjecture6322

#print axioms Conjecture6322.coefficient_sum
#print axioms Conjecture6322.term_expansion
#print axioms Conjecture6322.full_formula
#print axioms Conjecture6322.glynn_formula
#print axioms Conjecture6322.pairing_reduction
