import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Ring

/-!
# Definitions of tasks, classical causal models and ontological models

The paper is Yīng, Schmid and Spekkens, arXiv:2512.04173v5, and equation numbers are those of its
PDF. This file has definitions only. The statements about them are in
`PBRExclusion/Statements.lean`, and the proofs are in `PBRExclusion/Proofs/`.
`PBRExclusion/Results.lean` lists the main results.

Ontic state spaces are finite in this file, and probabilities are real numbers.
`PBRExclusion/GeneralDefs.lean` has the classical causal models again, with ontic states in any
probability space.

## Conventions

* A setting `s` is `0` for the Z-source and `1` for the X-source, and a source's outcome `x` is
  `0` or `1`. These are the paper's `S_A`, `S_B`, `X_A` and `X_B`. They are in `Fin 2`, where `+`
  is addition modulo 2.
* A label `(s, x)` names a state. `(0,0)` is `|0⟩`, `(0,1)` is `|1⟩`, `(1,0)` is `|+⟩` and
  `(1,1)` is `|-⟩`.
* A task `T` is one of the paper's `0+`, `0-`, `1+` and `1-`, written `![0,0]`, `![0,1]`,
  `![1,0]` and `![1,1]`. `T 0` says which state of the Z basis is in the paper's set `Ω_T`, and
  `T 1` says which state of the X basis.
* The outcome `(i, j)` of the joint measurement is the paper's `Y = 1 + 2 * i + j`, and `Y1` to
  `Y4` name the four. In the task `T` the outcome `(i, j)` excludes the product state `ρ_{Y|T}`,
  which has the label `(i, T i)` on qubit A and `(j, T j)` on qubit B.
* Ontic states are written `l`, `lA` and `lB`, because Lean reserves `λ`.
-/

namespace PBRExclusion

noncomputable section

variable {Λ ΛA ΛB : Type*} [Fintype Λ] [Fintype ΛA] [Fintype ΛB]

/-! ## Tasks, classical causal models and statistics -/

/-- `Pair` is the type of a pair of outcomes, one for each setting. -/
abbrev Pair := Fin 2 → Fin 2

/-- A task is the paper's `T`. `T 0` picks a state of the Z basis and `T 1` a state of the X basis,
and the two states are the paper's set `Ω_T`. -/
abbrev Task := Pair

/-- `Outcome` is the type of the joint measurement's outcome, the paper's `Y`. -/
abbrev Outcome := Fin 2 × Fin 2

/-- `Y1` is the paper's `Y = 1`. -/
abbrev Y1 : Outcome := (0, 0)

/-- `Y2` is the paper's `Y = 2`. -/
abbrev Y2 : Outcome := (0, 1)

/-- `Y3` is the paper's `Y = 3`. -/
abbrev Y3 : Outcome := (1, 0)

/-- `Y4` is the paper's `Y = 4`. -/
abbrev Y4 : Outcome := (1, 1)

/-- A **source** is a classical model of the paper's multi-source. It emits an ontic state `l`
with probability `p l`, and the ontic state goes to the joint measurement. Its response
`resp s l x` is the probability that it reports the outcome `x` under the setting `s`, and nothing
else enters that outcome. In the bilocality scenario it is a latent node together with the
multi-meter that has the setting. -/
structure Source (Λ : Type*) [Fintype Λ] where
  /-- `p l` is the probability of the ontic state `l`. -/
  p : Λ → ℝ
  /-- `resp s l x` is the probability of the outcome `x`, given the setting `s` and the ontic
  state `l`. -/
  resp : Fin 2 → Λ → Fin 2 → ℝ
  p_nonneg : ∀ l, 0 ≤ p l
  p_sum : ∑ l, p l = 1
  resp_nonneg : ∀ s l x, 0 ≤ resp s l x
  resp_sum : ∀ s l, ∑ x, resp s l x = 1

/-- A **classical causal model** within the bilocality scenario has two independent sources and a
joint measurement that sees both ontic states. Its response function `ξ T lA lB y` is the
probability of the outcome `y` in the task `T`, the paper's `ξ_{Y|T}(λ_A, λ_B)`. -/
structure Model (ΛA ΛB : Type*) [Fintype ΛA] [Fintype ΛB] where
  /-- `A` is the source of qubit A. -/
  A : Source ΛA
  /-- `B` is the source of qubit B. -/
  B : Source ΛB
  /-- `ξ T lA lB y` is the probability of the outcome `y` in the task `T`, given both ontic
  states. -/
  ξ : Task → ΛA → ΛB → Outcome → ℝ
  ξ_nonneg : ∀ T lA lB y, 0 ≤ ξ T lA lB y
  ξ_sum : ∀ T lA lB, ∑ y, ξ T lA lB y = 1

/-- The **statistics** of an experiment are the probabilities `P sA sB T xA xB y` of the outcomes
`xA`, `xB` and `y`, given the settings `sA` and `sB` and the task `T`. This is the paper's `ℙ(X_A
X_B Y | S_A S_B T)`. -/
abbrev Statistics := Fin 2 → Fin 2 → Task → Fin 2 → Fin 2 → Outcome → ℝ

/-- The statistics of a classical causal model are the average of the three responses over the two
independent ontic states. -/
def Model.statistics (M : Model ΛA ΛB) : Statistics := fun sA sB T xA xB y =>
  ∑ lA, ∑ lB, M.A.p lA * M.B.p lB *
    (M.A.resp sA lA xA * M.B.resp sB lB xB * M.ξ T lA lB y)

/-- The **forbidden mass** of a task adds up, over the task's four states, the probability that the
state is prepared and the outcome excludes it, each under the settings of that state. The state
`ρ_{Y|T}` with `Y = (i, j)` is prepared when the settings are `i` and `j` and the sources report `T
i` and `T j`. Conclusive exclusion is perfect when the forbidden mass is zero. -/
def forbidden (P : Statistics) (T : Task) : ℝ :=
  ∑ i, ∑ j, P i j T (T i) (T j) (i, j)

/-- `F4 P` is the forbidden mass of the four tasks together. -/
def F4 (P : Statistics) : ℝ := ∑ T : Task, forbidden P T

/-- `CE P T` is the paper's conclusiveness of exclusion for one task, `CE_T` of Eqs. (6) and (7). It
is one minus the average, over the task's four states, of the probability that the outcome excludes
the state, given that the state was prepared. The division conditions on the sources' outcomes. Lean
reads `x / 0` as `0`, so this is the paper's quantity only when each of the four states has positive
probability. -/
def CE (P : Statistics) (T : Task) : ℝ :=
  1 - 1 / 4 * ∑ i, ∑ j, P i j T (T i) (T j) (i, j) / ∑ y, P i j T (T i) (T j) y

/-- `CE4 P` is the paper's CE of Eq. (8), the average of `CE` over the four tasks. -/
def CE4 (P : Statistics) : ℝ := 1 / 4 * ∑ T : Task, CE P T

/-- `S.marginal s x` is the probability that the source reports `x` under the setting `s`. -/
def Source.marginal (S : Source Λ) (s x : Fin 2) : ℝ := ∑ l, S.p l * S.resp s l x

/-- A source has **unbiased outcomes** when each outcome has probability one half under each
setting, as the paper's Z-source and X-source have. This is a hypothesis of some theorems and never
part of the definition of a model. -/
def Source.Unbiased (S : Source Λ) : Prop := ∀ s x, S.marginal s x = 1 / 2

/-- The **joint overlap** of a source on a task is the probability mass on which the task's two
states cannot be told apart. It needs no assumption on the outcomes. With unbiased outcomes it is
half of the paper's `β_T` (`Source.β_eq`). -/
def Source.jointOverlap (S : Source Λ) (T : Task) : ℝ :=
  ∑ l, S.p l * min (S.resp 0 l (T 0)) (S.resp 1 l (T 1))

/-- `S.μ s x` is the paper's `μ` for a source. It is the distribution of the ontic state given that
the source reported `x` under the setting `s`, so `μ_0`, `μ_1`, `μ_+` and `μ_-` are `S.μ 0 0`, `S.μ
0 1`, `S.μ 1 0` and `S.μ 1 1`. Lean reads `x / 0` as `0`, so this is a distribution only when the
outcome has positive probability. -/
def Source.μ (S : Source Λ) (s x : Fin 2) (l : Λ) : ℝ :=
  S.p l * S.resp s l x / S.marginal s x

/-- `S.β T` is the paper's `β_T` for a source, (B14) and (B15) with a sum for the integral. It adds
up, over the ontic states, the smaller of the two distributions of the states in `Ω_T`. The paper
integrates over the intersection of the two ontic supports, and the smaller distribution is zero
outside it. -/
def Source.β (S : Source Λ) (T : Task) : ℝ := ∑ l, min (S.μ 0 (T 0) l) (S.μ 1 (T 1) l)

/-! ## The ontological model of Appendix B -/

/-- An `OntologicalModel` is the ontological model of Appendix B. A qubit has four distributions
over its ontic states, one for each label, and both qubits have the same four, as in the paper,
where `Λ_A × Λ_B = Λ × Λ`. The joint measurement of the task `T` has the response function
`ξ T`. -/
structure OntologicalModel (Λ : Type*) [Fintype Λ] where
  /-- `μ s x` is the distribution of the state with the label `(s, x)`. The paper's `μ_0`, `μ_1`,
  `μ_+` and `μ_-` are `μ 0 0`, `μ 0 1`, `μ 1 0` and `μ 1 1`. -/
  μ : Fin 2 → Fin 2 → Λ → ℝ
  /-- `ξ T lA lB y` is the probability of the outcome `y` in the task `T`, the paper's
  `ξ_{Y|T}(λ_A, λ_B)`. -/
  ξ : Task → Λ → Λ → Outcome → ℝ
  μ_nonneg : ∀ s x l, 0 ≤ μ s x l
  μ_sum : ∀ s x, ∑ l, μ s x l = 1
  ξ_nonneg : ∀ T lA lB y, 0 ≤ ξ T lA lB y
  ξ_sum : ∀ T lA lB, ∑ y, ξ T lA lB y = 1

/-- `N.Identity` is the ontological identity (B4), which says that the Z-source and the X-source
have the same average distribution. The paper derives it from the operational identity and
noncontextuality, and it is a hypothesis here. -/
def OntologicalModel.Identity (N : OntologicalModel Λ) : Prop :=
  ∀ l, 1 / 2 * N.μ 0 0 l + 1 / 2 * N.μ 0 1 l = 1 / 2 * N.μ 1 0 l + 1 / 2 * N.μ 1 1 l

/-- `N.CE T` is the conclusiveness of exclusion of the task `T` in this model, which is (B2) with
the probabilities of (B5). -/
def OntologicalModel.CE (N : OntologicalModel Λ) (T : Task) : ℝ :=
  1 - 1 / 4 * ∑ i, ∑ j, ∑ lA, ∑ lB, N.μ i (T i) lA * N.μ j (T j) lB * N.ξ T lA lB (i, j)

/-- `N.CE4` is the paper's CE in this model, the average of `N.CE` over the four tasks. -/
def OntologicalModel.CE4 (N : OntologicalModel Λ) : ℝ := 1 / 4 * ∑ T : Task, N.CE T

/-- `N.β T` is the paper's `β_T`, (B14) and (B15), with a sum for the integral. The paper integrates
over the intersection of the two ontic supports, and the smaller distribution is zero outside it. -/
def OntologicalModel.β (N : OntologicalModel Λ) (T : Task) : ℝ :=
  ∑ l, min (N.μ 0 (T 0) l) (N.μ 1 (T 1) l)

/-! ## Appendix B with distributions for each qubit

In the paper's prepare-measure scenario both qubits are prepared in the same states, and Appendix
B gives a state the same distribution on each, with `Λ_A × Λ_B = Λ × Λ`. In the bilocality
scenario of Appendix C a classical causal model has a source for each qubit. The model below is
for that case. It keeps the rest of Appendix B and gives each qubit its own four distributions,
and a classical causal model with unbiased outcomes is a model of this kind
(`Model.exists_ontologicalModelAB`). -/

/-- An `OntologicalModelAB` is an ontological model in which each qubit has its own ontic state
space and its own four distributions. -/
structure OntologicalModelAB (ΛA ΛB : Type*) [Fintype ΛA] [Fintype ΛB] where
  /-- `μA s x` is the distribution of qubit A's state with the label `(s, x)`. -/
  μA : Fin 2 → Fin 2 → ΛA → ℝ
  /-- `μB s x` is the distribution of qubit B's state with the label `(s, x)`. -/
  μB : Fin 2 → Fin 2 → ΛB → ℝ
  /-- `ξ T lA lB y` is the probability of the outcome `y` in the task `T`. -/
  ξ : Task → ΛA → ΛB → Outcome → ℝ
  μA_nonneg : ∀ s x l, 0 ≤ μA s x l
  μA_sum : ∀ s x, ∑ l, μA s x l = 1
  μB_nonneg : ∀ s x l, 0 ≤ μB s x l
  μB_sum : ∀ s x, ∑ l, μB s x l = 1
  ξ_nonneg : ∀ T lA lB y, 0 ≤ ξ T lA lB y
  ξ_sum : ∀ T lA lB, ∑ y, ξ T lA lB y = 1

/-- `N.Identity` says that each qubit satisfies the ontological identity (B4). -/
def OntologicalModelAB.Identity (N : OntologicalModelAB ΛA ΛB) : Prop :=
  (∀ l, 1 / 2 * N.μA 0 0 l + 1 / 2 * N.μA 0 1 l = 1 / 2 * N.μA 1 0 l + 1 / 2 * N.μA 1 1 l) ∧
    ∀ l, 1 / 2 * N.μB 0 0 l + 1 / 2 * N.μB 0 1 l = 1 / 2 * N.μB 1 0 l + 1 / 2 * N.μB 1 1 l

/-- `N.βA T` is the paper's `β_T` for qubit A. -/
def OntologicalModelAB.βA (N : OntologicalModelAB ΛA ΛB) (T : Task) : ℝ :=
  ∑ l, min (N.μA 0 (T 0) l) (N.μA 1 (T 1) l)

/-- `N.βB T` is the paper's `β_T` for qubit B. -/
def OntologicalModelAB.βB (N : OntologicalModelAB ΛA ΛB) (T : Task) : ℝ :=
  ∑ l, min (N.μB 0 (T 0) l) (N.μB 1 (T 1) l)

/-- `N.CE T` is the conclusiveness of exclusion of the task `T`, as in (B2) and (B5), with `μA` for
qubit A and `μB` for qubit B. -/
def OntologicalModelAB.CE (N : OntologicalModelAB ΛA ΛB) (T : Task) : ℝ :=
  1 - 1 / 4 * ∑ i, ∑ j, ∑ lA, ∑ lB, N.μA i (T i) lA * N.μB j (T j) lB * N.ξ T lA lB (i, j)

/-- `N.CE4` is the average of `N.CE` over the four tasks. -/
def OntologicalModelAB.CE4 (N : OntologicalModelAB ΛA ΛB) : ℝ := 1 / 4 * ∑ T : Task, N.CE T

/-- `N.toAB` is an ontological model of Appendix B as one with distributions for each qubit, in
which both qubits have the distributions `N.μ`. -/
def OntologicalModel.toAB (N : OntologicalModel Λ) : OntologicalModelAB Λ Λ where
  μA := N.μ
  μB := N.μ
  ξ := N.ξ
  μA_nonneg := N.μ_nonneg
  μA_sum := N.μ_sum
  μB_nonneg := N.μ_nonneg
  μB_sum := N.μ_sum
  ξ_nonneg := N.ξ_nonneg
  ξ_sum := N.ξ_sum

/-! ## The renaming of outcomes, and the outcome that never occurs on a state -/

/-- `relabel T` is how the task `T` renames the outcomes of the PBR measurement. For the tasks `0-`
and `1+` the outcomes `Y2` and `Y3` change places, and for `0+` and `1-` nothing changes. The
paper's four measurements are the PBR measurement with its outcomes renamed in this way
(`Quantum.effect_eq_pbr`). -/
def relabel (T : Task) (y : Outcome) : Outcome := if T 0 = T 1 then y else y.swap

/-- `impossibleOutcome sA xA sB xB` is the one outcome of the PBR measurement that never occurs when
qubit A has the label `(sA, xA)` and qubit B the label `(sB, xB)`. It is `(sA, sB)` when `xA` and
`xB` are equal and `(sA + 1, sB + 1)` when they differ (`Support.impossibleOutcome_eq`). That
quantum theory gives this outcome, and no other, probability zero is a theorem
(`Support.quantum_eq_zero_iff`) and not part of this definition. The arguments go qubit by qubit,
where `Statistics` takes the two settings first. -/
def impossibleOutcome (sA xA sB xB : Fin 2) : Outcome := (sA + xA + xB, sB + xA + xB)

/-! ## Explicit models

Each has sources whose ontic state fixes the outcome under both settings. -/

/-- A `DetSource` is a source with deterministic outcomes. It is given by a distribution `p` and,
for each ontic state, the outcome under each setting. -/
structure DetSource (Λ : Type*) [Fintype Λ] where
  /-- `p l` is the probability of the ontic state `l`. -/
  p : Λ → ℝ
  /-- `outcomes l s` is the outcome of the ontic state `l` under the setting `s`. -/
  outcomes : Λ → Pair
  p_nonneg : ∀ l, 0 ≤ p l
  p_sum : ∑ l, p l = 1

/-- `D.toSource` is the source that reports what its ontic state dictates. -/
def DetSource.toSource (D : DetSource Λ) : Source Λ where
  p := D.p
  resp s l x := if D.outcomes l s = x then 1 else 0
  p_nonneg := D.p_nonneg
  p_sum := D.p_sum
  resp_nonneg s l x := by split_ifs <;> norm_num
  resp_sum s l := by simp

/-- A sum over the four tasks can be written out term by term. This is a helper for the definitions
below. -/
theorem sum_pair (f : Pair → ℝ) :
    ∑ T : Task, f T = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp f]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, finTwoArrowEquiv]
  ring

/-- `bitSame` is a uniform bit that is reported under both settings, so `X = λ`. Bit 0 gives `|0⟩`
and `|+⟩`, and bit 1 gives `|1⟩` and `|-⟩`. -/
def bitSame : DetSource (Fin 2) where
  p _ := 1 / 2
  outcomes l _ := l
  p_nonneg _ := by norm_num
  p_sum := by norm_num

/-- `bitFlip` is a uniform bit that is reported under the setting 0 and flipped under the setting 1,
so `X = λ + S`. Bit 0 gives `|0⟩` and `|-⟩`, and bit 1 gives `|1⟩` and `|+⟩`. -/
def bitFlip : DetSource (Fin 2) where
  p _ := 1 / 2
  outcomes l s := l + s
  p_nonneg _ := by norm_num
  p_sum := by norm_num

/-- In the **two-bit model** each source emits a uniform bit. Source A is `bitSame`, so `X_A = λ_A`,
and source B is `bitFlip`, so `X_B = λ_B + S_B`. The joint measurement follows one rule in every
task. It gives `Y2` when the two bits are equal and `Y3` when they differ, and the task renames
these two as it renames the outcomes of the PBR measurement (`relabel`). So in the task `T` the
outcome is `Y2` when `λ_A + λ_B + T 0 + T 1 = 0` and `Y3` otherwise (`Support.twoBits_ξ_eq`). -/
def twoBits : Model (Fin 2) (Fin 2) where
  A := bitSame.toSource
  B := bitFlip.toSource
  ξ T lA lB y := if relabel T (lA + lB, lA + lB + 1) = y then 1 else 0
  ξ_nonneg _ _ _ _ := by split_ifs <;> norm_num
  ξ_sum _ _ _ := by simp

/-- `twoBitsAB` is the two-bit model as an ontological model with distributions for each qubit. On
qubit A the states `|0⟩` and `|+⟩` have the point distribution on bit 0, and `|1⟩` and `|-⟩` the one
on bit 1. On qubit B the states `|0⟩` and `|-⟩` have the point distribution on bit 0, and `|1⟩` and
`|+⟩` the one on bit 1. The response function is that of `twoBits`. -/
def twoBitsAB : OntologicalModelAB (Fin 2) (Fin 2) where
  μA _ x l := if l = x then 1 else 0
  μB s x l := if l + s = x then 1 else 0
  ξ := twoBits.ξ
  μA_nonneg _ _ _ := by split_ifs <;> norm_num
  μA_sum _ x := by simp
  μB_nonneg _ _ _ := by split_ifs <;> norm_num
  μB_sum s x := by
    simp only [Fin.sum_univ_two]
    fin_cases s <;> fin_cases x <;> simp (decide := true)
  ξ_nonneg := twoBits.ξ_nonneg
  ξ_sum := twoBits.ξ_sum

/-- `toyBit` is Spekkens' toy bit, whose ontic state is a pair of outcomes, uniformly distributed.
-/
def toyBit : DetSource Pair where
  p _ := 1 / 4
  outcomes l := l
  p_nonneg _ := by norm_num
  p_sum := by rw [sum_pair]; norm_num

/-- `biasedTrit` is a biased source with three ontic states, of probabilities 1/2, 1/4 and 1/4. The
first reports 0 under both settings. The second reports 1 under the setting 0 only, and the third
under the setting 1 only. -/
def biasedTrit : DetSource (Fin 3) where
  p := ![1 / 2, 1 / 4, 1 / 4]
  outcomes := ![![0, 0], ![1, 0], ![0, 1]]
  p_nonneg l := by fin_cases l <;> norm_num
  p_sum := by norm_num [Fin.sum_univ_three]

/-- `avoid outcomes T` is a setting whose state the source did not prepare, when there is one.
`outcomes` holds the source's outcomes under the two settings, and `T` is the task. If `outcomes i`
differs from `T i`, then the state of the setting `i` was not prepared, and excluding it is right.
If the outcomes are `T` itself there is no such setting, and the value is `T 0`. -/
def avoid (outcomes T : Task) : Fin 2 :=
  if outcomes 0 ≠ T 0 then 0 else if outcomes 1 ≠ T 1 then 1 else T 0

/-- `avoiding A B` is the model with two sources of deterministic outcomes and the joint measurement
that excludes, for each qubit, the state of the setting that `avoid` gives. The two models below are
of this kind. -/
def avoiding (A : DetSource ΛA) (B : DetSource ΛB) : Model ΛA ΛB where
  A := A.toSource
  B := B.toSource
  ξ T lA lB y := if (avoid (A.outcomes lA) T, avoid (B.outcomes lB) T) = y then 1 else 0
  ξ_nonneg T lA lB y := by split_ifs <;> norm_num
  ξ_sum T lA lB := by simp

/-- `twoBitsAlike` is the model with `bitSame` for both sources. Its CE is 7/8 (`twoBitsAlike_CE4`),
within the bound of 15/16 for two independent copies of one unbiased source (`Model.CE4_le`). -/
def twoBitsAlike : Model (Fin 2) (Fin 2) := avoiding bitSame bitSame

/-- `toy` is the model with the toy bit for both sources. Its CE is 15/16 (`toy_CE4`). -/
def toy : Model Pair Pair := avoiding toyBit toyBit

/-- `toyOntological` is the toy bit as an ontological model of Appendix B. The distribution of a
state is uniform over the two ontic states that give its outcome, and the measurement is `avoid`. It
is not the measurement of the paper's tight example before (B42), which reads only the outcomes
under the setting 0. Its CE is the same. -/
def toyOntological : OntologicalModel Pair where
  μ s x l := if l s = x then 1 / 2 else 0
  ξ T lA lB y := if (avoid lA T, avoid lB T) = y then 1 else 0
  μ_nonneg s x l := by split_ifs <;> norm_num
  μ_sum s x := by rw [sum_pair]; fin_cases s <;> fin_cases x <;> simp <;> norm_num
  ξ_nonneg T lA lB y := by split_ifs <;> norm_num
  ξ_sum T lA lB := by simp

end

end PBRExclusion
