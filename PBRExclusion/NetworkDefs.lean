import PBRExclusion.QuantumStatements

/-!
# Definitions of the experiment with two Bell pairs and steering

`PBRExclusion/QuantumDefs.lean` has the quantum statistics in prepare-measure form, where a
source's setting chooses which states it emits. Appendix C of the paper realizes each such
multi-source by steering. An entangled state has one half measured by a multi-meter, whose
setting chooses the basis, and the other half sent to the joint measurement. This file defines
quantum models of that kind, and the one in which the two entangled states are Bell pairs. The
statements are in `PBRExclusion/NetworkStatements.lean`.

## Conventions

* The four systems are in the order `A'`, `A`, `B`, `B'`. One entangled pair is on `A'` and `A`,
  and the other on `B` and `B'`. The multi-meters measure `A'` and `B'`, and the joint
  measurement measures `A` and `B`.
* Matrices are real, as in `PBRExclusion/QuantumDefs.lean`. A real symmetric positive matrix of
  trace one is a density matrix, and real positive matrices that sum to one are a measurement, so
  every model here is a quantum model. A quantum model with complex entries is not among them.
  That is harmless, because the file is used only to show that the model with two Bell pairs has
  the statistics of the prepare-measure experiment.
-/

namespace PBRExclusion.Quantum

open Matrix
open scoped Kronecker

noncomputable section

/-- A **quantum model** in the bilocality scenario has two independent entangled pairs, two
multi-meters and a joint measurement. One pair is in the state `srcA` of the systems `A'` and `A`,
and the other in the state `srcB` of `B` and `B'`. The multi-meter on `A'` has the effect
`meterA s x` for the outcome `x` under the setting `s`, and the multi-meter on `B'` likewise. The
joint measurement on `A` and `B` has the effect `meas T y` for the outcome `y` in the task `T`.
The types `α'`, `α`, `β`, `β'` index the bases of the four systems. -/
structure Model (α' α β β' : Type*) [Fintype α'] [Fintype α] [Fintype β] [Fintype β']
    [DecidableEq α'] [DecidableEq α] [DecidableEq β] [DecidableEq β'] where
  /-- `srcA` is the state of the first entangled pair, on `A'` and `A`. -/
  srcA : Matrix (α' × α) (α' × α) ℝ
  /-- `srcB` is the state of the second entangled pair, on `B` and `B'`. -/
  srcB : Matrix (β × β') (β × β') ℝ
  /-- `meterA s x` is the effect on `A'` for the outcome `x` under the setting `s`. -/
  meterA : Fin 2 → Fin 2 → Matrix α' α' ℝ
  /-- `meterB s x` is the effect on `B'` for the outcome `x` under the setting `s`. -/
  meterB : Fin 2 → Fin 2 → Matrix β' β' ℝ
  /-- `meas T y` is the joint measurement's effect on `A` and `B` for the outcome `y` in the task
  `T`. -/
  meas : Task → Outcome → Matrix (α × β) (α × β) ℝ
  srcA_posSemidef : srcA.PosSemidef
  srcA_trace : srcA.trace = 1
  srcB_posSemidef : srcB.PosSemidef
  srcB_trace : srcB.trace = 1
  meterA_posSemidef : ∀ s x, (meterA s x).PosSemidef
  meterA_sum : ∀ s, ∑ x, meterA s x = 1
  meterB_posSemidef : ∀ s x, (meterB s x).PosSemidef
  meterB_sum : ∀ s, ∑ x, meterB s x = 1
  meas_posSemidef : ∀ T y, (meas T y).PosSemidef
  meas_sum : ∀ T, ∑ y, meas T y = 1

variable {α' α β β' : Type*} [Fintype α'] [Fintype α] [Fintype β] [Fintype β']
  [DecidableEq α'] [DecidableEq α] [DecidableEq β] [DecidableEq β']

/-- `N.joint` is the three effects as one effect on the four systems, with the first multi-meter's
on `A'`, the joint measurement's on `A` and `B`, and the second multi-meter's on `B'`. The index
`((a', a), (b, b'))` follows the two pairs. -/
def Model.joint (N : Model α' α β β') (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) (y : Outcome) :
    Matrix ((α' × α) × (β × β')) ((α' × α) × (β × β')) ℝ :=
  Matrix.of fun i j =>
    N.meterA sA xA i.1.1 j.1.1 * N.meas T y (i.1.2, i.2.1) (j.1.2, j.2.1) *
      N.meterB sB xB i.2.2 j.2.2

/-- The statistics of such a model follow from Born's rule for the three effects on the product of
the two pairs' states. The product is what it means for the two sources to be independent. -/
def Model.statistics (N : Model α' α β β') : Statistics := fun sA sB T xA xB y =>
  (N.joint sA sB T xA xB y * (N.srcA ⊗ₖ N.srcB)).trace

/-! ## Two Bell pairs -/

/-- `bell` is the Bell pair `(|00⟩ + |11⟩)/√2` as a density matrix. -/
def bell : Matrix TwoQubits TwoQubits ℝ := proj fun k => if k.1 = k.2 then 1 else 0

/-- Under each setting the two states of a basis sum to the identity, so they are a measurement.
This theorem is a helper for the definition below. -/
theorem state_sum (s : Fin 2) : ∑ x, state s x = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := state_eq
  fin_cases s <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_two, h00, h01, h10, h11] <;> norm_num

/-- `bellModel` is the model with two Bell pairs. Each multi-meter measures its half in the Z basis
under the setting 0 and in the X basis under the setting 1, so its effect for the outcome `x` is the
projector of the label `(s, x)`. The joint measurement is the task's measurement of
`PBRExclusion/QuantumDefs.lean`. -/
def bellModel : Model (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  srcA := bell
  srcB := bell
  meterA := state
  meterB := state
  meas := effect
  srcA_posSemidef := Proofs.proj_posSemidef _
  srcA_trace := Proofs.proj_trace (by simp [dotProduct, Fintype.sum_prod_type])
  srcB_posSemidef := Proofs.proj_posSemidef _
  srcB_trace := Proofs.proj_trace (by simp [dotProduct, Fintype.sum_prod_type])
  meterA_posSemidef := state_posSemidef
  meterA_sum := state_sum
  meterB_posSemidef := state_posSemidef
  meterB_sum := state_sum
  meas_posSemidef := effect_posSemidef
  meas_sum := effect_sum

end

end PBRExclusion.Quantum
