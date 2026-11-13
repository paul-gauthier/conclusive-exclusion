import PBRExclusion.NetworkDefs

/-!
# Proofs for the experiment with two Bell pairs and steering

The statements are in `PBRExclusion/NetworkStatements.lean`.

* The Bell pair has entries one half where both index pairs are equal pairs (`bell_apply`).
* Tracing the three effects against two Bell pairs leaves a trace on the joint measurement's two
  qubits, with the multi-meters' effects transposed (`trace_joint_bell`).
* A projector is symmetric, so the transposes drop, and what is left is the prepare-measure
  statistics.
-/

namespace PBRExclusion.Quantum.Proofs

open Matrix
open scoped Kronecker

noncomputable section

/-! ## Every quantum model in the bilocality scenario -/

section General

variable {α' α β β' : Type*} [Fintype α'] [Fintype α] [Fintype β] [Fintype β']
  [DecidableEq α'] [DecidableEq α] [DecidableEq β] [DecidableEq β']

/-- The joint effects sum to the identity. -/
theorem joint_sum (N : Model α' α β β') (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, N.joint sA sB T xA xB y = 1 := by
  ext ⟨⟨i1, i2⟩, ⟨i3, i4⟩⟩ ⟨⟨j1, j2⟩, ⟨j3, j4⟩⟩
  have hA : ∑ x, N.meterA sA x i1 j1 = (1 : Matrix α' α' ℝ) i1 j1 := by
    rw [← N.meterA_sum sA, Matrix.sum_apply]
  have hB : ∑ x, N.meterB sB x i4 j4 = (1 : Matrix β' β' ℝ) i4 j4 := by
    rw [← N.meterB_sum sB, Matrix.sum_apply]
  have hC : ∑ y, N.meas T y (i2, i3) (j2, j3) =
      (1 : Matrix (α × β) (α × β) ℝ) (i2, i3) (j2, j3) := by
    rw [← N.meas_sum T, Matrix.sum_apply]
  simp only [Matrix.sum_apply, Model.joint, of_apply]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hA, hB, hC]
  simp only [Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;> by_cases h3 : i3 = j3 <;>
    by_cases h4 : i4 = j4 <;> simp [h1, h2, h3, h4]

theorem model_statistics_sum (N : Model α' α β β') (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, N.statistics sA sB T xA xB y = 1 := by
  simp only [Model.statistics, ← trace_sum, ← Finset.sum_mul]
  rw [joint_sum, Matrix.one_mul, trace_kronecker, N.srcA_trace, N.srcB_trace, mul_one]

end General

/-! ## Two Bell pairs -/

theorem bell_apply (k l : TwoQubits) :
    bell k l = if k.1 = k.2 ∧ l.1 = l.2 then 1 / 2 else 0 := by
  have h : (fun k : TwoQubits => if k.1 = k.2 then (1 : ℝ) else 0) ⬝ᵥ
      (fun k : TwoQubits => if k.1 = k.2 then (1 : ℝ) else 0) = 2 := by
    simp [dotProduct, Fintype.sum_prod_type]
  rw [bell, proj_apply, h]
  by_cases hk : k.1 = k.2 <;> by_cases hl : l.1 = l.2 <;> simp [hk, hl]

theorem proj_transpose {n : Type*} [Fintype n] (v : n → ℝ) : (proj v)ᵀ = proj v := by
  ext a b
  simp only [transpose_apply, proj_apply]
  ring

theorem state_transpose (s x : Fin 2) : (state s x)ᵀ = state s x := proj_transpose _

/-- For one multi-meter and its Bell pair, the trace over the pair leaves a trace on the joint
measurement's qubit, with the multi-meter's effect transposed. -/
theorem trace_kron_bell (S E : Matrix (Fin 2) (Fin 2) ℝ) :
    ((S ⊗ₖ E) * bell).trace = 1 / 2 * (E * Sᵀ).trace := by
  simp only [trace, diag_apply, mul_apply, kroneckerMap_apply, bell_apply, transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp
  ring

theorem bell_steering (s x : Fin 2) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    ((state s x ⊗ₖ E) * bell).trace = 1 / 2 * (E * state s x).trace := by
  rw [trace_kron_bell, state_transpose]

/-- Tracing the three effects against two Bell pairs leaves a trace on the joint measurement's two
qubits, with the multi-meters' effects transposed. -/
theorem trace_joint_bell (WA WB : Matrix (Fin 2) (Fin 2) ℝ) (E : Matrix TwoQubits TwoQubits ℝ) :
    ((Matrix.of fun i j : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
        WA i.1.1 j.1.1 * E (i.1.2, i.2.1) (j.1.2, j.2.1) * WB i.2.2 j.2.2) *
      (bell ⊗ₖ bell)).trace = 1 / 4 * (E * (WAᵀ ⊗ₖ WBᵀ)).trace := by
  simp only [trace, diag_apply, mul_apply, of_apply, kroneckerMap_apply, bell_apply,
    transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp
  ring

theorem bellModel_statistics : bellModel.statistics = statistics := by
  funext sA sB T xA xB y
  refine (trace_joint_bell (state sA xA) (state sB xB) (effect T y)).trans ?_
  rw [state_transpose, state_transpose, statistics, born]
  ring

end

end PBRExclusion.Quantum.Proofs
