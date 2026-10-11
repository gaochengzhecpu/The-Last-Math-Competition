import Main.Certificate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace Conjecture4215
set_option autoImplicit false
set_option maxRecDepth 10000
open Matrix

def triangle (t : T) : Finset V := {(face t).1, (face t).2.1, (face t).2.2}

/-- The complex contains every vertex and edge, and precisely the listed triangles. -/
def Faces (s : Finset V) : Prop := s.card ≤ 2 ∨ ∃ t, s = triangle t

theorem triangle_card : ∀ t, (triangle t).card = 3 := by decide +kernel
theorem triangle_injective : Function.Injective triangle := by decide +kernel
theorem all_edges_in_triangles : ∀ e, ∃ t, {(edge e).1, (edge e).2} ⊆ triangle t := by decide +kernel

theorem faces_downward_closed {s t : Finset V} (ht : Faces t) (hs : s ⊆ t) : Faces s := by
  rcases ht with ht | ⟨i, rfl⟩
  · exact Or.inl ((Finset.card_le_card hs).trans ht)
  · by_cases hc : s.card ≤ 2
    · exact Or.inl hc
    · refine Or.inr ⟨i, Finset.eq_of_subset_of_card_le hs ?_⟩
      rw [triangle_card]
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hc)

theorem facets_count : (Finset.univ.image triangle).card = 36 := by
  rw [Finset.card_image_of_injective _ triangle_injective]
  decide

theorem tree_face_count : Fintype.card T = Fintype.card E - Fintype.card V + 1 := by decide

/-- Extend an integer boundary matrix to rational chains. -/
def overQ {m n : Type*} (A : Matrix m n ℤ) : Matrix m n ℚ :=
  A.map (Int.castRingHom ℚ)

theorem overQ_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n ℤ) (B : Matrix n k ℤ) :
    overQ (A * B) = overQ A * overQ B := Matrix.map_mul

theorem overQ_add {m n : Type*} (A B : Matrix m n ℤ) :
    overQ (A + B) = overQ A + overQ B := by
  ext i j
  simp [overQ]

theorem overQ_zero {m n : Type*} : overQ (0 : Matrix m n ℤ) = 0 := by
  ext i j
  simp [overQ]

theorem overQ_eleven {n : Type*} [DecidableEq n] :
    overQ ((11 : ℤ) • (1 : Matrix n n ℤ)) = (11 : ℚ) • (1 : Matrix n n ℚ) := by
  ext i j
  change (((11 : ℤ) * (if i = j then 1 else 0) : ℤ) : ℚ) =
    (11 : ℚ) * (if i = j then 1 else 0)
  split_ifs <;> norm_num

theorem recovery_boundaryQ :
    overQ recovery * overQ d2 = (11 : ℚ) • (1 : Matrix T T ℚ) := by
  rw [← overQ_mul, recovery_boundary, overQ_eleven]

theorem homotopyQ :
    overQ d2 * overQ recovery + overQ treeLift * overQ d1 =
      (11 : ℚ) • (1 : Matrix E E ℚ) := by
  rw [← overQ_mul, ← overQ_mul, ← overQ_add, homotopy_identity, overQ_eleven]

theorem top_cycles_zero (z : T → ℤ) (hz : d2 *ᵥ z = 0) : z = 0 := by
  have h := congrArg (fun a : E → ℤ => recovery *ᵥ a) hz
  dsimp only at h
  rw [mulVec_mulVec, recovery_boundary, smul_mulVec_assoc, one_mulVec, mulVec_zero] at h
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, zsmul_eq_mul, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by norm_num)

theorem rational_top_cycles_zero (z : T → ℚ) (hz : overQ d2 *ᵥ z = 0) : z = 0 := by
  have h := congrArg (fun a : E → ℚ => overQ recovery *ᵥ a) hz
  dsimp only at h
  rw [mulVec_mulVec, recovery_boundaryQ, smul_mulVec_assoc, one_mulVec, mulVec_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem rational_cycle_is_boundary (z : E → ℚ) (hz : overQ d1 *ᵥ z = 0) :
    ∃ a : T → ℚ, overQ d2 *ᵥ a = z := by
  have h := congrArg (fun a : Matrix E E ℚ => a *ᵥ z) homotopyQ
  simp only [add_mulVec, ← mulVec_mulVec, hz, mulVec_zero, add_zero,
    smul_mulVec_assoc, one_mulVec] at h
  refine ⟨(1 / 11 : ℚ) • (overQ recovery *ᵥ z), ?_⟩
  rw [mulVec_smul, h, smul_smul]
  norm_num

theorem integer_cycle_multiple (z : E → ℤ) (hz : d1 *ᵥ z = 0) :
    ∃ a : T → ℤ, d2 *ᵥ a = (11 : ℤ) • z := by
  refine ⟨recovery *ᵥ z, ?_⟩
  have h := congrArg (fun a : Matrix E E ℤ => a *ᵥ z) homotopy_identity
  simpa only [add_mulVec, ← mulVec_mulVec, hz, mulVec_zero, add_zero,
    smul_mulVec_assoc, one_mulVec] using h

/-- The actual integral cycle lattice of the complete one-skeleton. -/
def cycles : AddSubgroup (E → ℤ) := (d1.mulVecLin.toAddMonoidHom).ker

theorem laplacian_cycle (z : E → ℤ) : d1 *ᵥ (laplacian *ᵥ z) = 0 := by
  rw [mulVec_mulVec, laplacian, ← Matrix.mul_assoc, boundary_squared, Matrix.zero_mul,
    Matrix.zero_mulVec]

/-- The up-down Laplacian as a map into the cycle lattice. -/
def lapMap : (E → ℤ) →+ cycles where
  toFun z := ⟨laplacian *ᵥ z, laplacian_cycle z⟩
  map_zero' := by apply Subtype.ext; exact mulVec_zero laplacian
  map_add' a b := by apply Subtype.ext; exact mulVec_add laplacian a b

def lapImage : AddSubgroup cycles := lapMap.range
abbrev Critical := cycles ⧸ lapImage

def witnessCycle : cycles := ⟨witness, witness_cycle⟩
def torsionClass : Critical := QuotientAddGroup.mk witnessCycle

theorem witness_not_laplacian (z : E → ℤ) : laplacian *ᵥ z ≠ witness := by
  intro hz
  have h := congrArg (fun v => detector ⬝ᵥ v) hz
  dsimp only at h
  rw [dotProduct_mulVec, detector_laplacian, smul_dotProduct, detector_pairing,
    zsmul_eq_mul] at h
  have hd : modulus ∣ (4081 : ℤ) := ⟨detectorMultiple ⬝ᵥ z, h.symm⟩
  norm_num [modulus] at hd

theorem torsion_nonzero : torsionClass ≠ 0 := by
  intro h
  have hm : witnessCycle ∈ lapImage := (QuotientAddGroup.eq_zero_iff _).mp h
  obtain ⟨z, hz⟩ := hm
  exact witness_not_laplacian z (congrArg Subtype.val hz)

theorem torsion_eleven : (11 : ℕ) • torsionClass = 0 := by
  change (11 : ℕ) • (QuotientAddGroup.mk' lapImage) witnessCycle = 0
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨preimage, ?_⟩
  apply Subtype.ext
  change laplacian *ᵥ preimage = (11 : ℕ) • witness
  simpa only [natCast_zsmul] using witness_multiple

def ambientImage : AddSubgroup (E → ℤ) := laplacian.mulVecLin.toAddMonoidHom.range
abbrev LapCokernel := (E → ℤ) ⧸ ambientImage

theorem cokernel_torsion :
    ∃ c : LapCokernel, c ≠ 0 ∧ (11 : ℕ) • c = 0 := by
  refine ⟨QuotientAddGroup.mk witness, ?_, ?_⟩
  · intro h
    have hm : witness ∈ ambientImage := (QuotientAddGroup.eq_zero_iff _).mp h
    obtain ⟨z, hz⟩ := hm
    exact witness_not_laplacian z hz
  · change (11 : ℕ) • (QuotientAddGroup.mk' ambientImage) witness = 0
    rw [← map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    refine ⟨preimage, ?_⟩
    change laplacian *ᵥ preimage = (11 : ℕ) • witness
    simpa only [natCast_zsmul] using witness_multiple

theorem witness_shape : witness = (11 : ℤ) • detectorMultiple := by decide +kernel
theorem certificate_symmetric : preimage = detector := by decide +kernel

/-- The chain conditions of a two-dimensional spanning tree, stated explicitly. -/
def IsTwoTree : Prop :=
  (∀ e, (edge e).1 < (edge e).2) ∧
  (∀ a b : V, a < b → ∃ e, edge e = (a,b)) ∧ Function.Injective edge ∧
  (∀ t, (face t).1 < (face t).2.1 ∧ (face t).2.1 < (face t).2.2) ∧
  Function.Injective face ∧
  (∀ z : T → ℤ, d2 *ᵥ z = 0 → z = 0) ∧
  (∀ z : E → ℚ, overQ d1 *ᵥ z = 0 → ∃ a : T → ℚ, overQ d2 *ᵥ a = z)

theorem is_two_tree : IsTwoTree :=
  ⟨edge_valid, edge_exhaustive, edge_unique, face_valid, face_unique,
    top_cycles_zero, rational_cycle_is_boundary⟩

/-- A prime larger than the number of vertices occurs as actual Laplacian torsion. -/
theorem counterexample : IsTwoTree ∧ Nat.Prime 11 ∧ 11 > Fintype.card V ∧
    ∃ c : Critical, c ≠ 0 ∧ (11 : ℕ) • c = 0 := by
  refine ⟨is_two_tree, by norm_num, by decide, torsionClass, torsion_nonzero, torsion_eleven⟩

#print axioms boundary_squared
#print axioms faces_downward_closed
#print axioms facets_count
#print axioms recovery_boundary
#print axioms homotopy_identity
#print axioms is_two_tree
#print axioms counterexample
#print axioms cokernel_torsion
end Conjecture4215
