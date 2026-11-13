import PBRExclusion.Proofs.Quantum

/-!
# Statements about the quantum experiment

Each statement in this file is proved. What follows its `:=` is the name of the proof in
`PBRExclusion/Proofs/Quantum.lean`, so the file can be read without the proofs.

The definitions are in `PBRExclusion/QuantumDefs.lean`. They are the four qubit states, the PBR
measurement, the measurement of each task, and the statistics that these give. `forbidden`, `F4`
and `CE4` are those of `PBRExclusion/Defs.lean`. The paper is Yīng, Schmid and Spekkens,
arXiv:2512.04173v5, and equation numbers are those of its PDF.
-/

namespace PBRExclusion.Quantum

open Matrix
open scoped Kronecker

noncomputable section

/-! ## The four states -/

/-- The four states are these matrices. -/
theorem state_eq :
    state 0 0 = !![1, 0; 0, 0] ∧ state 0 1 = !![0, 0; 0, 1] ∧
      state 1 0 = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] ∧
      state 1 1 = !![1 / 2, -1 / 2; -1 / 2, 1 / 2] := Proofs.state_eq

/-- Each state is positive semidefinite. -/
theorem state_posSemidef (s x : Fin 2) : (state s x).PosSemidef := Proofs.state_posSemidef s x

/-- Each state has trace one. -/
theorem state_trace (s x : Fin 2) : (state s x).trace = 1 := Proofs.state_trace s x

/-- Each state is pure. -/
theorem state_mul_self (s x : Fin 2) : state s x * state s x = state s x :=
  Proofs.state_mul_self s x

/-- This is the operational identity of Eq. (9). Averaged over its outcome, the Z-source and the
X-source emit the same state. -/
theorem state_identity :
    (1 / 2 : ℝ) • state 0 0 + (1 / 2 : ℝ) • state 0 1 =
      (1 / 2 : ℝ) • state 1 0 + (1 / 2 : ℝ) • state 1 1 := Proofs.state_identity

/-! ## The PBR measurement -/

/-- The four PBR vectors are these. The row is the basis state of qubit A and the column that of
qubit B. They are the vectors of Eq. (3) times `√2`, `2`, `2` and `2√2`. -/
theorem pbrKet_eq :
    (pbrKet (0, 0) = fun k => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (0, 1) = fun k => (!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (1, 0) = fun k => (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (1, 1) = fun k => (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) :=
  Proofs.pbrKet_eq

/-- Each effect of the PBR measurement is positive semidefinite. -/
theorem pbr_posSemidef (y : Outcome) : (pbr y).PosSemidef := Proofs.pbr_posSemidef y

/-- The four effects of the PBR measurement are orthogonal projectors. -/
theorem pbr_mul_pbr (y z : Outcome) : pbr y * pbr z = if y = z then pbr y else 0 :=
  Proofs.pbr_mul_pbr y z

/-- The effects of the PBR measurement sum to the identity, so it is a measurement in an orthonormal
basis. -/
theorem pbr_sum : ∑ y, pbr y = 1 := Proofs.pbr_sum

/-! ## The Paulis and the states of a task -/

/-- The four Paulis are these matrices. The last is `X * Z`, which is the paper's `Y` up to a phase.
-/
theorem pauli_eq :
    pauli ![0, 0] = 1 ∧ pauli ![0, 1] = pauliZ ∧ pauli ![1, 0] = pauliX ∧
      pauli ![1, 1] = !![0, -1; 1, 0] := Proofs.pauli_eq

/-- Each Pauli is an orthogonal matrix. -/
theorem pauli_mul_transpose (T : Task) : pauli T * (pauli T)ᵀ = 1 := Proofs.pauli_mul_transpose T

/-- The Pauli of the task `T` takes the state with the label `(s, x)` to the state with the label
`(s, x + T s)`. With `x = 0`, it takes the two states of `Ω_{0+}` to the two states of `Ω_T`. -/
theorem pauli_conj_state (T : Task) (s x : Fin 2) :
    pauli T * state s x * (pauli T)ᵀ = state s (x + T s) := Proofs.pauli_conj_state T s x

/-- This is Eq. (4). The state `ρ_{Y|T}` with `Y = (i, j)` is the state `ρ_{Y|0+}`, rotated by the
Pauli of the task on each qubit. -/
theorem task_state_eq (T : Task) (i j : Fin 2) :
    (pauli T ⊗ₖ pauli T) * (state i 0 ⊗ₖ state j 0) * (pauli T ⊗ₖ pauli T)ᵀ =
      state i (T i) ⊗ₖ state j (T j) := Proofs.task_state_eq T i j

/-! ## The measurement of a task -/

/-- Each effect of a task's measurement is positive semidefinite. -/
theorem effect_posSemidef (T : Task) (y : Outcome) : (effect T y).PosSemidef :=
  Proofs.effect_posSemidef T y

/-- The effects of a task's measurement sum to the identity. -/
theorem effect_sum (T : Task) : ∑ y, effect T y = 1 := Proofs.effect_sum T

/-- Renaming twice changes nothing, so `relabel T` is a permutation of the outcomes. -/
theorem relabel_relabel (T : Task) (y : Outcome) : relabel T (relabel T y) = y :=
  Proofs.relabel_relabel T y

/-! ## The statistics are a probability distribution -/

/-- The quantum statistics are nonnegative. -/
theorem statistics_nonneg (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) (y : Outcome) :
    0 ≤ statistics sA sB T xA xB y := Proofs.statistics_nonneg sA sB T xA xB y

/-- The quantum statistics sum to one over the three outcomes. -/
theorem statistics_sum (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, statistics sA sB T xA xB y = 1 := Proofs.statistics_sum sA sB T

/-- The outcomes of the two sources are unbiased and independent. Each pair of outcomes has
probability one quarter, whatever the settings and the task. This sum is the denominator in `CE`. -/
theorem sum_statistics (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) :
    ∑ y, statistics sA sB T xA xB y = 1 / 4 := Proofs.sum_statistics sA sB T xA xB

/-! ## The quantum value -/

/-- Conclusive exclusion is perfect in the quantum experiment. In every task the outcome `(i, j)`
never occurs on the state `ρ_{Y|T}` that it excludes. -/
theorem born_forbidden (T : Task) (i j : Fin 2) :
    born (effect T (i, j)) (state i (T i)) (state j (T j)) = 0 := Proofs.born_forbidden T i j

/-- The quantum statistics have no forbidden mass in any task. -/
theorem forbidden_statistics (T : Task) : forbidden statistics T = 0 :=
  Proofs.forbidden_statistics T

/-- The quantum statistics have no forbidden mass on the four tasks together. -/
theorem F4_statistics : F4 statistics = 0 := Proofs.F4_statistics

/-- Quantum theory reaches CE = 1, which is the paper's quantum value. -/
theorem CE4_statistics : CE4 statistics = 1 := Proofs.CE4_statistics

/-! ## The four measurements are the PBR measurement -/

/-- The measurement of each task is the PBR measurement with its outcomes renamed. For `0-` and `1+`
the outcomes `Y2` and `Y3` change places, and for `0+` and `1-` nothing changes. -/
theorem effect_eq_pbr (T : Task) (y : Outcome) : effect T y = pbr (relabel T y) :=
  Proofs.effect_eq_pbr T y

/-! ## Without the renaming -/

/-- Without the renaming, the outcome `Y2` of the PBR measurement occurs half the time on `|0⟩|-⟩`.
That state is `ρ_{2|0-}`, which the outcome `Y2` of the task `0-` excludes. -/
theorem born_pbr_control : born (pbr Y2) (state 0 0) (state 1 1) = 1 / 2 :=
  Proofs.born_pbr_control

end

end PBRExclusion.Quantum
