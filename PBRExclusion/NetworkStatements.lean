import PBRExclusion.Proofs.Network

/-!
# Statements about the experiment with two Bell pairs and steering

Each statement in this file is proved. What follows its `:=` is the name of the proof in
`PBRExclusion/Proofs/Network.lean`.

The definitions are in `PBRExclusion/NetworkDefs.lean`. `statistics` without a model is the
statistics of the prepare-measure experiment, from `PBRExclusion/QuantumDefs.lean`.
-/

namespace PBRExclusion.Quantum

open Matrix
open scoped Kronecker

noncomputable section

variable {α' α β β' : Type*} [Fintype α'] [Fintype α] [Fintype β] [Fintype β']
  [DecidableEq α'] [DecidableEq α] [DecidableEq β] [DecidableEq β']

/-! ## The model and the Bell pair -/

/-- In every such model the probabilities of the three outcomes sum to one. -/
theorem Model.statistics_sum (N : Model α' α β β') (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, N.statistics sA sB T xA xB y = 1 := Proofs.model_statistics_sum N sA sB T

/-- The Bell pair has weight one half on each of `|00⟩⟨00|`, `|00⟩⟨11|`, `|11⟩⟨00|` and `|11⟩⟨11|`.
-/
theorem bell_apply (k l : TwoQubits) :
    bell k l = if k.1 = k.2 ∧ l.1 = l.2 then 1 / 2 else 0 := Proofs.bell_apply k l

/-! ## Steering -/

/-- This is the steering step of Appendix C for a Bell pair. A multi-meter measures one half of the
pair and gets the projector of the label `(s, x)`. That happens with probability one half, and it
leaves the other half in the state with that label. For every effect `E` on the other half, the
joint probability is one half of the probability of `E` on that state. So a Bell pair and its
multi-meter together are a multi-source, as the paper says of an entangled state and a multi-meter.
-/
theorem bell_steering (s x : Fin 2) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    ((state s x ⊗ₖ E) * bell).trace = 1 / 2 * (E * state s x).trace := Proofs.bell_steering s x E

/-! ## The two forms of the experiment agree -/

/-- The model with two Bell pairs has the quantum statistics. -/
theorem bellModel_statistics : bellModel.statistics = statistics := Proofs.bellModel_statistics

end

end PBRExclusion.Quantum
