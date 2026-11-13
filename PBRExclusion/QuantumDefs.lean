import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import PBRExclusion.Defs

/-!
# Definitions of the quantum experiment

This is the paper's prepare-measure experiment. Under each setting a source emits one of two
qubit states, and the joint measurement measures the two qubits together. Its statistics have the
same `forbidden`, `CE` and `CE4` as those of a classical causal model, from
`PBRExclusion/Defs.lean`. The statements are in `PBRExclusion/QuantumStatements.lean`.

The paper is Yīng, Schmid and Spekkens, arXiv:2512.04173v5, and equation numbers are those of its
PDF. Eq. (2) has the four product states of the task `0+`, Eq. (3) the PBR basis, Eqs. (4) and
(5) the other three tasks, and Eq. (9) the operational identity.

## Conventions

* Every matrix is real, and every entry is rational. No `√2` appears, because a ket is kept
  without its normalization and `proj` divides by the squared norm. The Pauli `Y` enters only by
  conjugation, so the real matrix `X * Z` serves in its place.
* A qubit's basis is `|0⟩`, `|1⟩`. Two qubits are indexed by `(a, b)`, with qubit A first.
* Labels, tasks and outcomes are those of `PBRExclusion/Defs.lean`. The label `(s, x)` is `|0⟩`,
  `|1⟩`, `|+⟩`, `|-⟩` for `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`, and the outcome `(i, j)` is the
  paper's `Y = 1 + 2 * i + j`.
-/

namespace PBRExclusion.Quantum

open Matrix
open scoped Kronecker

noncomputable section

/-- `TwoQubits` indexes the basis of two qubits. The index `(a, b)` is the basis state `|a⟩` of
qubit A and `|b⟩` of qubit B. -/
abbrev TwoQubits := Fin 2 × Fin 2

/-- `ket s x` is the ket with the label `(s, x)`, not normalized. `ket 0 0` is `|0⟩`, `ket 0 1` is
`|1⟩`, `ket 1 0` is `|0⟩ + |1⟩` and `ket 1 1` is `|0⟩ - |1⟩`. -/
def ket : Fin 2 → Fin 2 → Fin 2 → ℝ := ![![![1, 0], ![0, 1]], ![![1, 1], ![1, -1]]]

/-- `proj v` is the projector onto the line through the vector `v`, which is `|v⟩⟨v| / ⟨v|v⟩`. -/
def proj {n : Type*} [Fintype n] (v : n → ℝ) : Matrix n n ℝ := (v ⬝ᵥ v)⁻¹ • vecMulVec v v

/-- `state s x` is the state with the label `(s, x)` as a density matrix, one of `|0⟩⟨0|`, `|1⟩⟨1|`,
`|+⟩⟨+|` and `|-⟩⟨-|`. -/
def state (s x : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ := proj (ket s x)

/-- `tensor u v` is the product ket `|u⟩|v⟩`, with `u` on qubit A and `v` on qubit B. -/
def tensor (u v : Fin 2 → ℝ) : TwoQubits → ℝ := fun k => u k.1 * v k.2

/-- `pbrKet` is the PBR basis of Eq. (3), not normalized. The vector of the outcome `(i, j)` is the
paper's `|φ_{Y|0+}⟩` with `Y = 1 + 2 * i + j`. The four lines of Eq. (3) are one formula, in which
the vector of `(i, j)` is the label `(i, 0)` on qubit A times `(j, 1)` on qubit B, plus `(i, 1)` on
qubit A times `(j, 0)` on qubit B. For `(0, 0)` that is `|0⟩|1⟩ + |1⟩|0⟩`, and for `(0, 1)` it is
`|0⟩|-⟩ + |1⟩|+⟩`. -/
def pbrKet (y : Outcome) : TwoQubits → ℝ :=
  tensor (ket y.1 0) (ket y.2 1) + tensor (ket y.1 1) (ket y.2 0)

/-- `pbr` is the PBR measurement, the paper's `ℳ_{0+}`. The effect of the outcome `y` is the
projector onto the PBR vector of `y`. -/
def pbr (y : Outcome) : Matrix TwoQubits TwoQubits ℝ := proj (pbrKet y)

/-- `pauliX` is the Pauli `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- `pauliZ` is the Pauli `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `pauli T` is the Pauli of a task, which takes the two states of `Ω_{0+}` to the two states of
`Ω_T`. It has an `X` when `T` picks `|1⟩`, then a `Z` when `T` picks `|-⟩`. So it is `1` for `0+`,
`Z` for `0-`, `X` for `1+`, and `X * Z` for `1-`, where the paper has `Y`. -/
def pauli (T : Task) : Matrix (Fin 2) (Fin 2) ℝ := pauliX ^ (T 0).val * pauliZ ^ (T 1).val

/-- `effect T y` is the measurement of a task, the paper's `E_{Y|T}` of Eq. (5). It is the PBR
measurement rotated by the Pauli of the task on each qubit. -/
def effect (T : Task) (y : Outcome) : Matrix TwoQubits TwoQubits ℝ :=
  (pauli T ⊗ₖ pauli T) * pbr y * (pauli T ⊗ₖ pauli T)ᵀ

/-- `born E ρA ρB` is Born's rule for a product state, the probability of the effect `E` when qubit
A is in the state `ρA` and qubit B in the state `ρB`. -/
def born (E : Matrix TwoQubits TwoQubits ℝ) (ρA ρB : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (E * (ρA ⊗ₖ ρB)).trace

/-- The **quantum statistics** are those of the paper's experiment. Under the setting `s` a source
emits the state with the label `(s, 0)` or `(s, 1)`, each with probability one half, and reports
which as its outcome. The two qubits then meet the task's measurement. -/
def statistics : Statistics := fun sA sB T xA xB y =>
  1 / 2 * (1 / 2) * born (effect T y) (state sA xA) (state sB xB)

end

end PBRExclusion.Quantum
