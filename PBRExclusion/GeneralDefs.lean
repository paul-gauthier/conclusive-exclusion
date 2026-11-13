import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import PBRExclusion.Defs

/-!
# Definitions of classical causal models with ontic states in any probability space

An ontic state space is any measurable space here, and a source has any probability measure on
it. `PBRExclusion/Defs.lean` has the same definitions for finite ontic state spaces. The
statements are in `PBRExclusion/GeneralStatements.lean`.

Three things change from the finite definitions.

* A source has a probability measure `ν`, where the finite definition has a function `p` that
  sums to one.
* Each response is a measurable function of the ontic state.
* The statistics are an integral over the product measure `A.ν.prod B.ν`. The product is what
  it means for the two sources to be independent.

Tasks, outcomes and statistics do not change, and neither do `forbidden`, `F4`, `CE` and `CE4`,
which are functions of the statistics alone. So a theorem here is about the same CE as the finite
one. `Source.ofFinite` and `Model.ofFinite` read a finite model as one of these.
-/

namespace PBRExclusion.General

open MeasureTheory

noncomputable section

variable {Λ ΛA ΛB : Type*} [MeasurableSpace Λ] [MeasurableSpace ΛA] [MeasurableSpace ΛB]

/-- A **source** whose ontic state lives in any probability space emits an ontic state `l` with
the distribution `ν`. Its response `resp s l x` is the probability that it reports the outcome `x`
under the setting `s`, and nothing else enters that outcome. -/
structure Source (Λ : Type*) [MeasurableSpace Λ] where
  /-- `ν` is the distribution of the ontic state. -/
  ν : Measure Λ
  /-- `resp s l x` is the probability of the outcome `x`, given the setting `s` and the ontic
  state `l`. -/
  resp : Fin 2 → Λ → Fin 2 → ℝ
  ν_prob : IsProbabilityMeasure ν
  resp_measurable : ∀ s x, Measurable fun l => resp s l x
  resp_nonneg : ∀ s l x, 0 ≤ resp s l x
  resp_sum : ∀ s l, ∑ x, resp s l x = 1

attribute [instance] Source.ν_prob

/-- A **classical causal model** within the bilocality scenario, with ontic states in any two
probability spaces, has two independent sources and a joint measurement that sees both ontic
states. Its response function `ξ T lA lB y` is the probability of the outcome `y` in the task
`T`, and it is measurable in the two ontic states together. -/
structure Model (ΛA ΛB : Type*) [MeasurableSpace ΛA] [MeasurableSpace ΛB] where
  /-- `A` is the source of qubit A. -/
  A : Source ΛA
  /-- `B` is the source of qubit B. -/
  B : Source ΛB
  /-- `ξ T lA lB y` is the probability of the outcome `y` in the task `T`, given both ontic
  states. -/
  ξ : Task → ΛA → ΛB → Outcome → ℝ
  ξ_measurable : ∀ T y, Measurable fun l : ΛA × ΛB => ξ T l.1 l.2 y
  ξ_nonneg : ∀ T lA lB y, 0 ≤ ξ T lA lB y
  ξ_sum : ∀ T lA lB, ∑ y, ξ T lA lB y = 1

/-- The statistics of a classical causal model are the average of the three responses over the two
ontic states. The two are independent, so the average is over the product of the two sources'
measures. -/
def Model.statistics (M : Model ΛA ΛB) : Statistics := fun sA sB T xA xB y =>
  ∫ l, M.A.resp sA l.1 xA * M.B.resp sB l.2 xB * M.ξ T l.1 l.2 y ∂(M.A.ν.prod M.B.ν)

/-- `S.marginal s x` is the probability that the source reports `x` under the setting `s`. -/
def Source.marginal (S : Source Λ) (s x : Fin 2) : ℝ := ∫ l, S.resp s l x ∂S.ν

/-- A source has **unbiased outcomes** when each outcome has probability one half under each
setting. This is a hypothesis of some theorems and never part of the definition of a model. -/
def Source.Unbiased (S : Source Λ) : Prop := ∀ s x, S.marginal s x = 1 / 2

/-- The **joint overlap** of a source on a task is the probability mass on which the task's two
states cannot be told apart. With unbiased outcomes it is half of the paper's `β_T`. -/
def Source.jointOverlap (S : Source Λ) (T : Task) : ℝ :=
  ∫ l, min (S.resp 0 l (T 0)) (S.resp 1 l (T 1)) ∂S.ν

/-! ## Finite models as models of this kind -/

/-- `Source.ofFinite S` is a finite source as a source of this kind. It puts the mass `S.p l` on the
ontic state `l`, the responses are the same, and every set of ontic states is measurable. -/
def Source.ofFinite [Fintype Λ] [MeasurableSingletonClass Λ] (S : PBRExclusion.Source Λ) :
    Source Λ where
  ν := ∑ l, ENNReal.ofReal (S.p l) • Measure.dirac l
  resp := S.resp
  ν_prob := ⟨by
    simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => S.p_nonneg l, S.p_sum, ENNReal.ofReal_one]⟩
  resp_measurable _ _ := measurable_of_finite _
  resp_nonneg := S.resp_nonneg
  resp_sum := S.resp_sum

/-- `Model.ofFinite M` is a finite model as a model of this kind, with the same two sources and the
same response function. -/
def Model.ofFinite [Fintype ΛA] [Fintype ΛB] [MeasurableSingletonClass ΛA]
    [MeasurableSingletonClass ΛB] (M : PBRExclusion.Model ΛA ΛB) : Model ΛA ΛB where
  A := Source.ofFinite M.A
  B := Source.ofFinite M.B
  ξ := M.ξ
  ξ_measurable _ _ := measurable_of_finite _
  ξ_nonneg := M.ξ_nonneg
  ξ_sum := M.ξ_sum

end

end PBRExclusion.General
