import PBRExclusion.Proofs.Support

/-!
# Statements about the two-bit model and the support of the quantum statistics

Each statement in this file is proved. What follows its `:=` is the name of the proof in
`PBRExclusion/Proofs/Support.lean`, so the file can be read without the proofs.

`Model` is the classical causal model with finite ontic state spaces, and `General.Model` is the
one with ontic states in any probability spaces. `Quantum.statistics` is the statistics of the
quantum experiment, and `Quantum.bellModel` is the same experiment with two Bell pairs and
steering. The two-bit model `twoBits`, the renaming `relabel` and the rule `impossibleOutcome`
are defined in `PBRExclusion/Defs.lean`.

An event is a setting for each source, a task and the three outcomes. An impossible event of some
statistics is an event of probability zero, and the support is the set of the other events.
-/

namespace PBRExclusion.Support

open MeasureTheory

noncomputable section

/-! ## The two-bit model has CE = 1 -/

/-- Both sources of the two-bit model have unbiased outcomes. -/
theorem twoBits_unbiased : twoBits.A.Unbiased ∧ twoBits.B.Unbiased := Proofs.twoBits_unbiased

/-- The joint measurement of the two-bit model gives `Y2` in the task `T` when
`λ_A + λ_B + T 0 + T 1 = 0`, and `Y3` otherwise. -/
theorem twoBits_ξ_eq (T : Task) (lA lB : Fin 2) (y : Outcome) :
    twoBits.ξ T lA lB y = if y = (lA + lB + T 0 + T 1, lA + lB + T 0 + T 1 + 1) then 1 else 0 :=
  Proofs.twoBits_ξ_eq T lA lB y

/-- The joint measurement of the two-bit model never gives `Y1` or `Y4`. -/
theorem twoBits_ξ_Y1_Y4 (T : Task) (lA lB : Fin 2) :
    twoBits.ξ T lA lB Y1 = 0 ∧ twoBits.ξ T lA lB Y4 = 0 := Proofs.twoBits_ξ_Y1_Y4 T lA lB

/-- The joint measurement of the two-bit model follows one rule that each task renames. It gives
`Y2` when the two bits are equal and `Y3` when they differ, and the task renames the outcome as
it renames the outcomes of the PBR measurement. -/
theorem twoBits_ξ (T : Task) (lA lB : Fin 2) (z : Outcome) :
    twoBits.ξ T lA lB (relabel T z) = if (lA + lB, lA + lB + 1) = z then 1 else 0 :=
  Proofs.twoBits_ξ T lA lB z

/-- In the two-bit model each product state is prepared with probability one quarter, whatever
the task, so the conditional probabilities in `CE` are defined. -/
theorem twoBits_prepared (T : Task) (sA sB xA xB : Fin 2) :
    ∑ y, twoBits.statistics sA sB T xA xB y = 1 / 4 := Proofs.twoBits_prepared T sA sB xA xB

/-- In the two-bit model the paper's state `ρ_{2|T}`, which has the settings `(0, 1)` and the
outcomes `(T 0, T 1)`, has probability one quarter, and all of it goes to `Y3`. -/
theorem twoBits_state2 (T : Task) : twoBits.statistics 0 1 T (T 0) (T 1) Y3 = 1 / 4 :=
  Proofs.twoBits_state2 T

/-- In the two-bit model the state `ρ_{3|T}`, which has the settings `(1, 0)` and the outcomes
`(T 1, T 0)`, has probability one quarter, and all of it goes to `Y2`. -/
theorem twoBits_state3 (T : Task) : twoBits.statistics 1 0 T (T 1) (T 0) Y2 = 1 / 4 :=
  Proofs.twoBits_state3 T

/-- In each task the two-bit model has no forbidden mass, so the outcome never excludes the state
that was prepared. -/
theorem twoBits_forbidden (T : Task) : forbidden twoBits.statistics T = 0 :=
  Proofs.twoBits_forbidden T

/-- The two-bit model has no forbidden mass on the four tasks together. -/
theorem twoBits_F4 : F4 twoBits.statistics = 0 := Proofs.twoBits_F4

/-- The two-bit model has `CE_T = 1` in each task. -/
theorem twoBits_CE (T : Task) : CE twoBits.statistics T = 1 := Proofs.twoBits_CE T

/-- The CE of Eq. (8) is 1 for the two-bit model. -/
theorem twoBits_CE4 : CE4 twoBits.statistics = 1 := Proofs.twoBits_CE4

/-! ## The two-bit model as an ontological model with distributions for each qubit -/

/-- The distributions of `twoBitsAB` are the `μ` of the two sources of the two-bit model. -/
theorem twoBitsAB_μ (s x l : Fin 2) :
    twoBitsAB.μA s x l = twoBits.A.μ s x l ∧ twoBitsAB.μB s x l = twoBits.B.μ s x l :=
  Proofs.twoBitsAB_μ s x l

/-- In `twoBitsAB` each qubit satisfies the ontological identity (B4). -/
theorem twoBitsAB_identity : twoBitsAB.Identity := Proofs.twoBitsAB_identity

/-- In `twoBitsAB`, `CE_T` is 1 in each task. -/
theorem twoBitsAB_CE (T : Task) : twoBitsAB.CE T = 1 := Proofs.twoBitsAB_CE T

/-- In `twoBitsAB` the average of CE over the four tasks is 1. -/
theorem twoBitsAB_CE4 : twoBitsAB.CE4 = 1 := Proofs.twoBitsAB_CE4

/-- The two sources of the two-bit model give `|+⟩` different distributions. Its distribution is
all on bit 0 at source A and all on bit 1 at source B. -/
theorem twoBits_μ_plus : twoBits.A.μ 1 0 0 = 1 ∧ twoBits.B.μ 1 0 0 = 0 := Proofs.twoBits_plus

/-! ## The impossible events of the quantum statistics -/

/-- The impossible outcome of a product state is `(sA, sB)` when the two sources' outcomes are
equal, and the opposite outcome `(sA + 1, sB + 1)` when they differ. -/
theorem impossibleOutcome_eq (sA xA sB xB : Fin 2) :
    impossibleOutcome sA xA sB xB = if xA = xB then (sA, sB) else (sA + 1, sB + 1) :=
  Proofs.impossibleOutcome_eq sA xA sB xB

/-- In the task `T` an event has probability zero in the quantum statistics exactly when its
outcome `y`, renamed as the task renames it, is the impossible outcome of its product state. Each
of the sixteen product states has one, so each task has sixteen impossible events among its
64. -/
theorem quantum_eq_zero_iff (T : Task) (sA sB xA xB : Fin 2) (y : Outcome) :
    Quantum.statistics sA sB T xA xB y = 0 ↔ relabel T y = impossibleOutcome sA xA sB xB :=
  Proofs.quantum_eq_zero_iff T sA sB xA xB y

/-- Every impossible event of the quantum statistics is an impossible event of the two-bit
model. -/
theorem twoBits_impossible_events (T : Task) (sA sB xA xB : Fin 2) (y : Outcome)
    (h : Quantum.statistics sA sB T xA xB y = 0) :
    twoBits.statistics sA sB T xA xB y = 0 := Proofs.twoBits_keeps T sA sB xA xB y h

/-! ## The support of the quantum statistics

A classical causal model in which every impossible event of the quantum statistics is impossible
also gives probability zero to an event that quantum theory allows. -/

/-- In the task `0+`, quantum theory gives the state `|0⟩|0⟩` both `Y2` and `Y3`. Each of the two
events has probability 1/16, which is one quarter for the state times one quarter for the
outcome. -/
theorem quantum_state00 :
    Quantum.statistics 0 0 ![0, 0] 0 0 Y2 = 1 / 16 ∧
      Quantum.statistics 0 0 ![0, 0] 0 0 Y3 = 1 / 16 := Proofs.quantum_state00

/-- In the task `0+`, the two-bit model gives the state `|0⟩|0⟩` the outcome `Y2` every time, so
that event has probability one quarter, and it never gives that state `Y3`. -/
theorem twoBits_state00 :
    twoBits.statistics 0 0 ![0, 0] 0 0 Y2 = 1 / 4 ∧
      twoBits.statistics 0 0 ![0, 0] 0 0 Y3 = 0 := Proofs.twoBits_state00

section Finite

variable {ΛA ΛB : Type*} [Fintype ΛA] [Fintype ΛB]

/-- If a classical causal model with finite ontic state spaces gives probability zero, in some
task, to the impossible outcome of each of the sixteen product states, then on the state
`|0⟩|0⟩` it gives probability zero to `Y2` or to `Y3`. -/
theorem not_both_finite (M : Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0) :
    M.statistics 0 0 T 0 0 Y2 = 0 ∨ M.statistics 0 0 T 0 0 Y3 = 0 :=
  Proofs.not_both_finite M T h

end Finite

section General

variable {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB]

/-- If a classical causal model, with ontic states in any probability spaces, gives probability
zero, in some task, to the impossible outcome of each of the sixteen product states, then on the
state `|0⟩|0⟩` it gives probability zero to `Y2` or to `Y3`. -/
theorem not_both (M : General.Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0) :
    M.statistics 0 0 T 0 0 Y2 = 0 ∨ M.statistics 0 0 T 0 0 Y3 = 0 := Proofs.not_both M T h

/-- No classical causal model, with ontic states in any probability spaces, has exactly the
support of the quantum statistics in the single task `0+`. -/
theorem support_not_classical_one_task :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ sA sB xA xB y,
      (M.statistics sA sB ![0, 0] xA xB y = 0 ↔
        Quantum.statistics sA sB ![0, 0] xA xB y = 0) := Proofs.zeroPlus_not_classical

/-- No classical causal model within the bilocality scenario, with ontic states in any
probability spaces, has exactly the support of the quantum statistics on the four tasks. This is
a possibilistic gap, and it uses the possible events as well as the impossible ones. -/
theorem support_not_classical :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ T sA sB xA xB y,
      (M.statistics sA sB T xA xB y = 0 ↔ Quantum.statistics sA sB T xA xB y = 0) :=
  Proofs.support_not_classical

/-- No classical causal model within the bilocality scenario has exactly the support of the
statistics of the experiment with two Bell pairs and steering. -/
theorem bellModel_not_classical :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ T sA sB xA xB y,
      (M.statistics sA sB T xA xB y = 0 ↔
        Quantum.bellModel.statistics sA sB T xA xB y = 0) := Proofs.bellModel_not_classical

end General

/-! ## The two-bit model with ontic states in probability spaces -/

/-- The two-bit model, as a classical causal model with ontic states in probability spaces, has
unbiased outcomes, every impossible event of the quantum statistics, no forbidden mass, and
CE = 1. -/
theorem ofFinite_twoBits :
    (General.Model.ofFinite twoBits).A.Unbiased ∧ (General.Model.ofFinite twoBits).B.Unbiased ∧
      (∀ T sA sB xA xB y, Quantum.statistics sA sB T xA xB y = 0 →
        (General.Model.ofFinite twoBits).statistics sA sB T xA xB y = 0) ∧
      F4 (General.Model.ofFinite twoBits).statistics = 0 ∧
      CE4 (General.Model.ofFinite twoBits).statistics = 1 := Proofs.ofFinite_twoBits

end

end PBRExclusion.Support
