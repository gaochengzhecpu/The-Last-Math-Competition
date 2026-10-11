import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Tauto

/-! A coefficient-free type A₂ exchange graph and the Weyl-group obstruction. -/
namespace Conjecture565

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option autoImplicit false

abbrev P := MvPolynomial (Fin 2) ℚ
abbrev F := FractionRing P
abbrev I := Fin 5

noncomputable section

def x : P := MvPolynomial.X 0
def y : P := MvPolynomial.X 1
def ev : P →+* ℚ := MvPolynomial.eval₂Hom (RingHom.id ℚ) ![2, 5]
def emb : P →+* F := algebraMap P F

local instance : DecidableEq F := Classical.decEq _

def num : I → P := ![x, y, 1 + y, 1 + x + y, 1 + x]
def den : I → P := ![1, 1, x, x * y, y]
def clusterVar (i : I) : F := emb (num i) / emb (den i)

theorem ev_num_ne (i : I) : ev (num i) ≠ 0 := by
  fin_cases i <;> norm_num [ev, num, x, y, MvPolynomial.eval₂Hom]

theorem ev_den_ne (i : I) : ev (den i) ≠ 0 := by
  fin_cases i <;> norm_num [ev, den, x, y, MvPolynomial.eval₂Hom]

theorem num_ne (i : I) : num i ≠ 0 := by
  intro h
  exact ev_num_ne i (by rw [h, map_zero])

theorem den_ne (i : I) : den i ≠ 0 := by
  intro h
  exact ev_den_ne i (by rw [h, map_zero])

theorem emb_ne {p : P} (h : p ≠ 0) : emb p ≠ 0 := by
  exact fun e => h (IsFractionRing.injective P F (by simpa [emb] using e))

theorem clusterVar_ne (i : I) : clusterVar i ≠ 0 :=
  div_ne_zero (emb_ne (num_ne i)) (emb_ne (den_ne i))

theorem clusterVar_injective : Function.Injective clusterVar := by
  intro i j h
  have hc := (div_eq_div_iff (emb_ne (den_ne i)) (emb_ne (den_ne j))).mp h
  have hp : num i * den j = num j * den i :=
    IsFractionRing.injective P F (by simpa [emb] using hc)
  have he := congrArg ev hp
  fin_cases i <;> fin_cases j <;>
    norm_num [ev, num, den, x, y, MvPolynomial.eval₂Hom] at he ⊢

def next (i : I) : I := i + 1
def prev (i : I) : I := i - 1

theorem next_prev (i : I) : next (prev i) = i := by fin_cases i <;> decide
theorem prev_next (i : I) : prev (next i) = i := by fin_cases i <;> decide
theorem next_ne (i : I) : next i ≠ i := by fin_cases i <;> decide

theorem exchange_relation (i : I) :
    clusterVar i * clusterVar (next (next i)) = 1 + clusterVar (next i) := by
  have hx : emb x ≠ 0 := emb_ne (by simpa [den] using den_ne 2)
  have hy : emb y ≠ 0 := emb_ne (by simpa [den] using den_ne 4)
  fin_cases i
  · change emb x / emb 1 * (emb (1 + y) / emb x) = 1 + emb y / emb 1
    simp only [map_one, map_add, div_one]
    field_simp [hx]
  · change emb y / emb 1 * (emb (1 + x + y) / emb (x * y)) =
      1 + emb (1 + y) / emb x
    simp only [map_one, map_add, map_mul, div_one]
    field_simp [hx, hy]; ring
  · change emb (1 + y) / emb x * (emb (1 + x) / emb y) =
      1 + emb (1 + x + y) / emb (x * y)
    simp only [map_one, map_add, map_mul]
    field_simp [hx, hy]; ring
  · change emb (1 + x + y) / emb (x * y) * (emb x / emb 1) =
      1 + emb (1 + x) / emb y
    simp only [map_one, map_add, map_mul, div_one]
    field_simp [hx, hy]; ring
  · change emb (1 + x) / emb y * (emb y / emb 1) = 1 + emb x / emb 1
    simp only [map_one, map_add, div_one]
    field_simp [hy]

theorem mutate_next (i : I) :
    (1 + clusterVar (next i)) / clusterVar i = clusterVar (next (next i)) := by
  apply (div_eq_iff (clusterVar_ne i)).mpr
  rw [mul_comm, exchange_relation]

theorem mutate_prev (i : I) :
    (1 + clusterVar i) / clusterVar (next i) = clusterVar (prev i) := by
  apply (div_eq_iff (clusterVar_ne (next i))).mpr
  simpa only [next_prev] using (exchange_relation (prev i)).symm

def cluster (i : I) : Finset F := {clusterVar i, clusterVar (next i)}

theorem mem_cluster (a : F) (i : I) :
    a ∈ cluster i ↔ a = clusterVar i ∨ a = clusterVar (next i) := by
  simp [cluster]

theorem cluster_injective : Function.Injective cluster := by
  intro i j h
  have hi : clusterVar i ∈ cluster j := by rw [← h]; simp [cluster]
  have hn : clusterVar (next i) ∈ cluster j := by rw [← h]; simp [cluster]
  rw [mem_cluster] at hi hn
  have h1 : i = j ∨ i = next j := hi.imp (fun h => clusterVar_injective h) (fun h => clusterVar_injective h)
  have h2 : next i = j ∨ next i = next j := hn.imp (fun h => clusterVar_injective h) (fun h => clusterVar_injective h)
  fin_cases i <;> fin_cases j <;> norm_num [next] at h1 h2 ⊢ <;> tauto

/-- Replace one clusterVar in a two-element cluster using the A₂ exchange relation. -/
def Mutates (S T : Finset F) : Prop :=
  ∃ a b : F, a ≠ b ∧ a ≠ 0 ∧ S = {a, b} ∧ T = {(1 + b) / a, b}

theorem mutation_classification (i : I) (T : Finset F) :
    Mutates (cluster i) T ↔ T = cluster (next i) ∨ T = cluster (prev i) := by
  constructor
  · rintro ⟨a, b, hab, ha, hs, ht⟩
    have ma : a ∈ cluster i := by rw [hs]; simp
    have mb : b ∈ cluster i := by rw [hs]; simp
    rw [mem_cluster] at ma mb
    rcases ma with rfl | rfl <;> rcases mb with rfl | rfl
    · exact False.elim (hab rfl)
    · left
      rw [ht, mutate_next]
      simp [cluster, Finset.pair_comm]
    · right
      rw [ht, mutate_prev]
      simp [cluster, next_prev]
    · exact False.elim (hab rfl)
  · rintro (rfl | rfl)
    · refine ⟨clusterVar i, clusterVar (next i), ?_, clusterVar_ne i, rfl, ?_⟩
      · exact fun h => next_ne i (clusterVar_injective h).symm
      · rw [mutate_next]; simp [cluster, Finset.pair_comm]
    · refine ⟨clusterVar (next i), clusterVar i, ?_, clusterVar_ne (next i), ?_, ?_⟩
      · exact fun h => next_ne i (clusterVar_injective h)
      · simp [cluster, Finset.pair_comm]
      · rw [mutate_prev]; simp [cluster, next_prev]

/-- All clusters reached from the initial seed by a finite sequence of mutations. -/
inductive Reachable : Finset F → Prop
  | initial : Reachable (cluster 0)
  | step {S T} : Reachable S → Mutates S T → Reachable T

theorem reachable_next (i : I) (h : Reachable (cluster i)) :
    Reachable (cluster (next i)) :=
  h.step ((mutation_classification i _).mpr (Or.inl rfl))

theorem all_clusters_reachable (i : I) : Reachable (cluster i) := by
  have h0 : Reachable (cluster 0) := .initial
  have h1 : Reachable (cluster 1) := reachable_next 0 h0
  have h2 : Reachable (cluster 2) := reachable_next 1 h1
  have h3 : Reachable (cluster 3) := reachable_next 2 h2
  have h4 : Reachable (cluster 4) := reachable_next 3 h3
  fin_cases i <;> assumption

theorem reachable_iff (S : Finset F) : Reachable S ↔ ∃ i, S = cluster i := by
  constructor
  · intro h
    induction h with
    | initial => exact ⟨0, rfl⟩
    | @step S T _ ht ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases (mutation_classification i T).mp ht with h | h
      · exact ⟨next i, h⟩
      · exact ⟨prev i, h⟩
  · rintro ⟨i, rfl⟩
    exact all_clusters_reachable i

def Adj (i j : I) : Prop := j = next i ∨ j = prev i

instance (i j : I) : Decidable (Adj i j) := inferInstanceAs (Decidable (_ ∨ _))

theorem mutation_iff_adj (i j : I) : Mutates (cluster i) (cluster j) ↔ Adj i j := by
  rw [mutation_classification]
  simp only [cluster_injective.eq_iff, Adj]

theorem adj_symm : ∀ i j, Adj i j ↔ Adj j i := by decide
theorem adj_irrefl : ∀ i, ¬ Adj i i := by decide

abbrev States := {S : Finset F // Reachable S}

def state (i : I) : States := ⟨cluster i, all_clusters_reachable i⟩

def stateEquiv : I ≃ States := Equiv.ofBijective state (by
  constructor
  · intro i j h
    exact cluster_injective (congrArg Subtype.val h)
  · rintro ⟨S, hS⟩
    obtain ⟨i, rfl⟩ := (reachable_iff S).mp hS
    exact ⟨i, rfl⟩)

theorem states_card : Nat.card States = 5 := by
  rw [← Nat.card_congr stateEquiv]
  simp [I]

def automorphisms {V : Type*} (R : V → V → Prop) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ i j, R (p i) (p j) ↔ R i j}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro p q hp hq i j
    exact (hp (q i) (q j)).trans (hq i j)
  inv_mem' := by
    intro p hp i j
    simpa using (hp (p⁻¹ i) (p⁻¹ j)).symm

def cycleAut := automorphisms Adj
def exchangeAut := automorphisms (fun S T : States => Mutates S.val T.val)

def autEquiv : cycleAut ≃ exchangeAut :=
  (stateEquiv.permCongr).subtypeEquiv (by
    intro p
    change (∀ i j, Adj (p i) (p j) ↔ Adj i j) ↔
      (∀ S T, Mutates ((stateEquiv.permCongr p) S).val
        ((stateEquiv.permCongr p) T).val ↔ Mutates S.val T.val)
    constructor
    · intro h S T
      obtain ⟨i, rfl⟩ := stateEquiv.surjective S
      obtain ⟨j, rfl⟩ := stateEquiv.surjective T
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      change Mutates (cluster (p i)) (cluster (p j)) ↔ Mutates (cluster i) (cluster j)
      simpa only [mutation_iff_adj] using h i j
    · intro h i j
      have he := h (stateEquiv i) (stateEquiv j)
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at he
      change Mutates (cluster (p i)) (cluster (p j)) ↔ Mutates (cluster i) (cluster j) at he
      simpa only [mutation_iff_adj] using he)

instance : Fintype cycleAut :=
  inferInstanceAs (Fintype {p : Equiv.Perm I // ∀ i j, Adj (p i) (p j) ↔ Adj i j})

theorem cycle_aut_card : Fintype.card cycleAut = 10 := by decide

theorem exchange_aut_card : Nat.card exchangeAut = 10 := by
  rw [← Nat.card_congr autEquiv, Nat.card_eq_fintype_card, cycle_aut_card]

/-- The standard roots eᵢ - eⱼ of A₂. -/
def root (i j k : Fin 3) : ℚ := (if k = i then 1 else 0) - (if k = j then 1 else 0)

/-- The reflection in eᵢ - eⱼ, written using its squared norm 2. -/
def reflection (i j : Fin 3) (v : Fin 3 → ℚ) (k : Fin 3) : ℚ :=
  v k - (v i - v j) * root i j k

theorem reflection_is_swap (i j : Fin 3) (hij : i ≠ j) (v : Fin 3 → ℚ) :
    reflection i j v = fun k => v (Equiv.swap i j k) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [reflection, root, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst k
      simp [reflection, root, hij, Ne.symm hij]
    · simp [reflection, root, hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem root_length (i j : Fin 3) (hij : i ≠ j) :
    ∑ k : Fin 3, root i j k * root i j k = 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [root, Fin.sum_univ_succ] at hij ⊢ <;> norm_num

theorem root_pairing (i j : Fin 3) (v : Fin 3 → ℚ) :
    ∑ k : Fin 3, v k * root i j k = v i - v j := by
  fin_cases i <;> fin_cases j <;> simp [root, Fin.sum_univ_succ] <;> ring

theorem simple_roots_cartan :
    (∑ k : Fin 3, root 0 1 k * root 1 2 k) = -1 := by
  simp [root, Fin.sum_univ_succ]

def s0 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def s1 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

def WeylA2 : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.closure {s0, s1}

def sixWords : Finset (Equiv.Perm (Fin 3)) :=
  {1, s0, s1, s0 * s1, s1 * s0, s0 * s1 * s0}

theorem six_words_exhaust : ∀ p : Equiv.Perm (Fin 3), p ∈ sixWords := by decide

theorem weyl_eq_top : WeylA2 = ⊤ := by
  apply top_unique
  intro p _
  have h0 : s0 ∈ WeylA2 := Subgroup.subset_closure (by simp)
  have h1 : s1 ∈ WeylA2 := Subgroup.subset_closure (by simp)
  have h := six_words_exhaust p
  simp only [sixWords, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact WeylA2.one_mem
  · exact h0
  · exact h1
  · exact WeylA2.mul_mem h0 h1
  · exact WeylA2.mul_mem h1 h0
  · exact WeylA2.mul_mem (WeylA2.mul_mem h0 h1) h0

theorem weyl_card : Nat.card WeylA2 = 6 := by
  calc
    Nat.card WeylA2 = Nat.card (Equiv.Perm (Fin 3)) :=
      Nat.card_congr ((MulEquiv.subgroupCongr weyl_eq_top).trans (Subgroup.topEquiv)).toEquiv
    _ = 6 := by rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide

theorem no_weyl_embedding (f : WeylA2 →* exchangeAut) :
    ¬ Function.Injective f := by
  intro hf
  have h := Subgroup.card_dvd_of_injective f hf
  rw [exchange_aut_card, weyl_card] at h
  norm_num at h

theorem no_semidirect_description (H : Type*) [Group H]
    (φ : H →* MulAut WeylA2) :
    IsEmpty (exchangeAut ≃* WeylA2 ⋊[φ] H) := by
  refine ⟨fun e => ?_⟩
  exact no_weyl_embedding (e.symm.toMonoidHom.comp SemidirectProduct.inl)
    (e.symm.injective.comp SemidirectProduct.inl_injective)

#print axioms clusterVar_injective
#print axioms exchange_relation
#print axioms mutation_classification
#print axioms reachable_iff
#print axioms exchange_aut_card
#print axioms reflection_is_swap
#print axioms root_length
#print axioms root_pairing
#print axioms weyl_card
#print axioms no_semidirect_description

end
end Conjecture565

