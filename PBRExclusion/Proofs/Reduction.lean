import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import PBRExclusion.GeneralDefs
import PBRExclusion.Proofs.AppendixB

/-!
# Proofs of the reduction to finite models

Every classical causal model, with ontic states in any two probability spaces, has the statistics of
a finite model whose ontic states are pairs of outcomes (`pairModel_statistics`). The bound for any
probability space is then the finite one, applied to that model. The statements are in
`PBRExclusion/GeneralStatements.lean`.

For a source and a pair of outcomes `τ`, the weight of `τ` at the ontic state `l` is `resp 0 l (τ 0)
* resp 1 l (τ 1)`. It is the probability that the source would report `τ 0` under the setting 0 and
`τ 1` under the setting 1, with the two outcomes drawn independently.

* The finite source has the ontic state `τ` with probability `∫ weight τ`, and it reports `τ s`
  under the setting `s`.
* The finite model's response function, given `τA` and `τB`, is the average of the response function
  over the ontic states, weighted by the two weights.

Everything integrated here is measurable and between 0 and 1, so it is integrable.
-/

namespace PBRExclusion.General.Proofs

open MeasureTheory

noncomputable section

variable {Λ ΛA ΛB : Type*} [MeasurableSpace Λ] [MeasurableSpace ΛA] [MeasurableSpace ΛB]

/-! ## Bounded measurable functions are integrable -/

theorem integrable_of_unit {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {f : α → ℝ} (hm : Measurable f) (h0 : ∀ a, 0 ≤ f a) (h1 : ∀ a, f a ≤ 1) : Integrable f ν :=
  Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun a => by
    rw [Real.norm_of_nonneg (h0 a)]
    exact h1 a)

/-! ## Responses -/

theorem resp_add (S : Source Λ) (s : Fin 2) (l : Λ) : S.resp s l 0 + S.resp s l 1 = 1 := by
  simpa [Fin.sum_univ_two] using S.resp_sum s l

theorem resp_le_one (S : Source Λ) (s : Fin 2) (l : Λ) (x : Fin 2) : S.resp s l x ≤ 1 :=
  calc S.resp s l x ≤ ∑ x, S.resp s l x :=
        Finset.single_le_sum (fun i _ => S.resp_nonneg s l i) (Finset.mem_univ x)
    _ = 1 := S.resp_sum s l

theorem ξ_le_one (M : Model ΛA ΛB) (T : Task) (lA : ΛA) (lB : ΛB) (y : Outcome) :
    M.ξ T lA lB y ≤ 1 :=
  calc M.ξ T lA lB y ≤ ∑ y, M.ξ T lA lB y :=
        Finset.single_le_sum (fun i _ => M.ξ_nonneg T lA lB i) (Finset.mem_univ y)
    _ = 1 := M.ξ_sum T lA lB

/-- A product of two numbers between 0 and 1 is at most 1. -/
theorem mul_le_one_of_unit {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

/-! ## The weight of a pair -/

/-- The weight of the pair `τ` at the ontic state `l`. -/
def weight (S : Source Λ) (τ : Pair) (l : Λ) : ℝ := S.resp 0 l (τ 0) * S.resp 1 l (τ 1)

theorem weight_nonneg (S : Source Λ) (τ : Pair) (l : Λ) : 0 ≤ weight S τ l :=
  mul_nonneg (S.resp_nonneg _ _ _) (S.resp_nonneg _ _ _)

theorem weight_le_one (S : Source Λ) (τ : Pair) (l : Λ) : weight S τ l ≤ 1 :=
  mul_le_one_of_unit (resp_le_one S _ _ _) (S.resp_nonneg _ _ _) (resp_le_one S _ _ _)

theorem measurable_weight (S : Source Λ) (τ : Pair) : Measurable (weight S τ) :=
  (S.resp_measurable 0 (τ 0)).mul (S.resp_measurable 1 (τ 1))

theorem integrable_weight (S : Source Λ) (τ : Pair) : Integrable (weight S τ) S.ν :=
  integrable_of_unit (measurable_weight S τ) (weight_nonneg S τ) (weight_le_one S τ)

/-- The weights of the pairs that have the outcome `x` under the setting `s` add up to the response.
-/
theorem sum_weight_ite (S : Source Λ) (s x : Fin 2) (l : Λ) :
    ∑ τ : Pair, (if τ s = x then weight S τ l else 0) = S.resp s l x := by
  have h0 := resp_add S 0 l
  have h1 := resp_add S 1 l
  rw [sum_pair]
  rcases PBRExclusion.Proofs.fin_two_cases s with rfl | rfl <;>
    rcases PBRExclusion.Proofs.fin_two_cases x with rfl | rfl <;> simp [weight]
  · linear_combination S.resp 0 l 0 * h1
  · linear_combination S.resp 0 l 1 * h1
  · linear_combination S.resp 1 l 0 * h0
  · linear_combination S.resp 1 l 1 * h0

/-- At each ontic state the four weights add up to one. -/
theorem sum_weight (S : Source Λ) (l : Λ) : ∑ τ : Pair, weight S τ l = 1 := by
  have h0 := resp_add S 0 l
  have h1 := resp_add S 1 l
  rw [sum_pair]
  simp only [weight, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (S.resp 1 l 0 + S.resp 1 l 1) * h0 + h1

/-! ## The finite source -/

/-- The finite source, whose ontic state is a pair of outcomes with the probability of its weight.
-/
def pairSource (S : Source Λ) : DetSource Pair where
  p τ := ∫ l, weight S τ l ∂S.ν
  outcomes τ := τ
  p_nonneg τ := integral_nonneg fun l => weight_nonneg S τ l
  p_sum := by
    rw [← integral_finsetSum _ fun τ _ => integrable_weight S τ]
    simp [sum_weight]

/-- The finite source reports with the same probabilities. -/
theorem pairSource_marginal (S : Source Λ) (s x : Fin 2) :
    (pairSource S).toSource.marginal s x = S.marginal s x := by
  have h : ∀ τ : Pair, (pairSource S).p τ * (if τ s = x then (1 : ℝ) else 0) =
      ∫ l, (if τ s = x then weight S τ l else 0) ∂S.ν := fun τ => by
    by_cases hτ : τ s = x <;> simp [hτ, pairSource]
  simp only [PBRExclusion.Source.marginal, DetSource.toSource, Source.marginal]
  simp_rw [show ∀ τ : Pair, (pairSource S).outcomes τ = τ from fun _ => rfl, h]
  rw [← integral_finsetSum _ fun τ _ => by
    by_cases hτ : τ s = x
    · simpa [hτ] using integrable_weight S τ
    · simp [hτ]]
  simp_rw [sum_weight_ite]

/-! ## The finite joint measurement -/

/-- The integrand of the finite measurement's average, which is the two weights times the response
function. -/
def kernel (M : Model ΛA ΛB) (T : Task) (y : Outcome) (τA τB : Pair) (l : ΛA × ΛB) : ℝ :=
  weight M.A τA l.1 * weight M.B τB l.2 * M.ξ T l.1 l.2 y

theorem kernel_nonneg (M : Model ΛA ΛB) (T : Task) (y : Outcome) (τA τB : Pair) (l : ΛA × ΛB) :
    0 ≤ kernel M T y τA τB l :=
  mul_nonneg (mul_nonneg (weight_nonneg _ _ _) (weight_nonneg _ _ _)) (M.ξ_nonneg _ _ _ _)

theorem kernel_le_one (M : Model ΛA ΛB) (T : Task) (y : Outcome) (τA τB : Pair) (l : ΛA × ΛB) :
    kernel M T y τA τB l ≤ 1 :=
  mul_le_one_of_unit
    (mul_le_one_of_unit (weight_le_one _ _ _) (weight_nonneg _ _ _) (weight_le_one _ _ _))
    (M.ξ_nonneg _ _ _ _) (ξ_le_one M _ _ _ _)

theorem measurable_kernel (M : Model ΛA ΛB) (T : Task) (y : Outcome) (τA τB : Pair) :
    Measurable (kernel M T y τA τB) :=
  (((measurable_weight M.A τA).comp measurable_fst).mul
    ((measurable_weight M.B τB).comp measurable_snd)).mul (M.ξ_measurable T y)

theorem integrable_kernel (M : Model ΛA ΛB) (T : Task) (y : Outcome) (τA τB : Pair) :
    Integrable (kernel M T y τA τB) (M.A.ν.prod M.B.ν) :=
  integrable_of_unit (measurable_kernel M T y τA τB) (kernel_nonneg M T y τA τB)
    (kernel_le_one M T y τA τB)

/-- This is the numerator of the finite model's response function. -/
def num (M : Model ΛA ΛB) (T : Task) (τA τB : Pair) (y : Outcome) : ℝ :=
  ∫ l, kernel M T y τA τB l ∂(M.A.ν.prod M.B.ν)

theorem num_nonneg (M : Model ΛA ΛB) (T : Task) (τA τB : Pair) (y : Outcome) :
    0 ≤ num M T τA τB y :=
  integral_nonneg fun l => kernel_nonneg M T y τA τB l

/-- Over the four outcomes the numerators add up to the product of the two pairs' probabilities.
This is Fubini's theorem for a product of two functions. -/
theorem sum_num (M : Model ΛA ΛB) (T : Task) (τA τB : Pair) :
    ∑ y, num M T τA τB y = (pairSource M.A).p τA * (pairSource M.B).p τB := by
  simp only [num]
  rw [← integral_finsetSum _ fun y _ => integrable_kernel M T y τA τB]
  simp only [kernel, ← Finset.mul_sum, M.ξ_sum, mul_one]
  exact integral_prod_mul (weight M.A τA) (weight M.B τB)

theorem num_le (M : Model ΛA ΛB) (T : Task) (τA τB : Pair) (y : Outcome) :
    num M T τA τB y ≤ (pairSource M.A).p τA * (pairSource M.B).p τB := by
  rw [← sum_num M T τA τB]
  exact Finset.single_le_sum (fun i _ => num_nonneg M T τA τB i) (Finset.mem_univ y)

/-- The finite model has the finite sources. Its response function, given the two pairs, is the
average of the response function over the ontic states, weighted by the two weights. Where the two
pairs have probability zero the average is not defined, and the response function gives each of the
four outcomes probability one quarter. -/
def pairModel (M : Model ΛA ΛB) : PBRExclusion.Model Pair Pair where
  A := (pairSource M.A).toSource
  B := (pairSource M.B).toSource
  ξ T τA τB y :=
    if (pairSource M.A).p τA * (pairSource M.B).p τB = 0 then 1 / 4
    else num M T τA τB y / ((pairSource M.A).p τA * (pairSource M.B).p τB)
  ξ_nonneg T τA τB y := by
    split_ifs
    · norm_num
    · exact div_nonneg (num_nonneg M T τA τB y)
        (mul_nonneg ((pairSource M.A).p_nonneg τA) ((pairSource M.B).p_nonneg τB))
  ξ_sum T τA τB := by
    by_cases h : (pairSource M.A).p τA * (pairSource M.B).p τB = 0
    · simp only [ite_eq_left h]
      rw [Fintype.sum_prod_type]
      norm_num
    · simp only [ite_eq_right h]
      rw [← Finset.sum_div, sum_num, div_self h]

/-- The probability of the two pairs times the finite model's response function is the numerator.
Where the probability is zero, so is the numerator. -/
theorem p_mul_ξ (M : Model ΛA ΛB) (T : Task) (τA τB : Pair) (y : Outcome) :
    (pairSource M.A).p τA * (pairSource M.B).p τB * (pairModel M).ξ T τA τB y =
      num M T τA τB y := by
  by_cases h : (pairSource M.A).p τA * (pairSource M.B).p τB = 0
  · have h0 : num M T τA τB y = 0 :=
      le_antisymm (h ▸ num_le M T τA τB y) (num_nonneg M T τA τB y)
    simp [pairModel, h, h0]
  · have h' : (pairSource M.A).p τA * (pairSource M.B).p τB ≠ 0 := h
    simp only [pairModel, ite_eq_right h]
    rw [mul_div_assoc', mul_div_cancel_left₀ _ h']

/-! ## The statistics agree -/

/-- The integrand of the statistics, as a sum over the pairs of both sources. -/
theorem integrand_eq (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) (y : Outcome)
    (l : ΛA × ΛB) :
    M.A.resp sA l.1 xA * M.B.resp sB l.2 xB * M.ξ T l.1 l.2 y =
      ∑ τA : Pair, ∑ τB : Pair,
        (if τA sA = xA then (1 : ℝ) else 0) * (if τB sB = xB then 1 else 0) *
          kernel M T y τA τB l := by
  rw [← sum_weight_ite M.A sA xA l.1, ← sum_weight_ite M.B sB xB l.2, Finset.sum_mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun τA _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τB _ => ?_
  unfold kernel
  split_ifs <;> ring

/-- The finite model has the statistics of the model that it was built from. -/
theorem pairModel_statistics (M : Model ΛA ΛB) : (pairModel M).statistics = M.statistics := by
  funext sA sB T xA xB y
  have hL : (pairModel M).statistics sA sB T xA xB y =
      ∑ τA : Pair, ∑ τB : Pair,
        (if τA sA = xA then (1 : ℝ) else 0) * (if τB sB = xB then 1 else 0) *
          num M T τA τB y := by
    simp only [PBRExclusion.Model.statistics]
    refine Finset.sum_congr rfl fun τA _ => Finset.sum_congr rfl fun τB _ => ?_
    rw [← p_mul_ξ M T τA τB y]
    change (pairSource M.A).p τA * (pairSource M.B).p τB *
      ((if τA sA = xA then (1 : ℝ) else 0) * (if τB sB = xB then 1 else 0) *
        (pairModel M).ξ T τA τB y) = _
    ring
  have hi : ∀ τA τB : Pair, Integrable (fun l =>
      (if τA sA = xA then (1 : ℝ) else 0) * (if τB sB = xB then 1 else 0) *
        kernel M T y τA τB l) (M.A.ν.prod M.B.ν) :=
    fun τA τB => (integrable_kernel M T y τA τB).const_mul _
  rw [hL]
  simp only [Model.statistics, integrand_eq M sA sB T xA xB y]
  rw [integral_finsetSum _ fun τA _ => integrable_finsetSum _ fun τB _ => hi τA τB]
  refine Finset.sum_congr rfl fun τA _ => ?_
  rw [integral_finsetSum _ fun τB _ => hi τA τB]
  refine Finset.sum_congr rfl fun τB _ => ?_
  rw [integral_const_mul, num]

theorem pairModel_marginal_A (M : Model ΛA ΛB) (s x : Fin 2) :
    (pairModel M).A.marginal s x = M.A.marginal s x := pairSource_marginal M.A s x

theorem pairModel_marginal_B (M : Model ΛA ΛB) (s x : Fin 2) :
    (pairModel M).B.marginal s x = M.B.marginal s x := pairSource_marginal M.B s x

theorem pairModel_unbiased_A (M : Model ΛA ΛB) (h : M.A.Unbiased) : (pairModel M).A.Unbiased :=
  fun s x => (pairModel_marginal_A M s x).trans (h s x)

theorem pairModel_unbiased_B (M : Model ΛA ΛB) (h : M.B.Unbiased) : (pairModel M).B.Unbiased :=
  fun s x => (pairModel_marginal_B M s x).trans (h s x)

/-- One source for both qubits stays one source for both qubits. -/
theorem pairModel_A_eq_B (M : Model Λ Λ) (h : M.A = M.B) : (pairModel M).A = (pairModel M).B := by
  change (pairSource M.A).toSource = (pairSource M.B).toSource
  rw [h]

theorem exists_pair_model (M : Model ΛA ΛB) :
    ∃ N : PBRExclusion.Model Pair Pair, N.statistics = M.statistics ∧
      (∀ s x, N.A.marginal s x = M.A.marginal s x) ∧
      ∀ s x, N.B.marginal s x = M.B.marginal s x :=
  ⟨pairModel M, pairModel_statistics M, pairModel_marginal_A M, pairModel_marginal_B M⟩

theorem exists_pair_model_of_eq (M : Model Λ Λ) (h : M.A = M.B) :
    ∃ N : PBRExclusion.Model Pair Pair, N.A = N.B ∧ N.statistics = M.statistics ∧
      ∀ s x, N.A.marginal s x = M.A.marginal s x :=
  ⟨pairModel M, pairModel_A_eq_B M h, pairModel_statistics M, pairModel_marginal_A M⟩

/-! ## What follows from the finite theorems -/

theorem statistics_nonneg (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2)
    (y : Outcome) : 0 ≤ M.statistics sA sB T xA xB y := by
  rw [← pairModel_statistics M]
  exact PBRExclusion.Proofs.statistics_nonneg _ sA sB T xA xB y

theorem statistics_sum (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, M.statistics sA sB T xA xB y = 1 := by
  rw [← pairModel_statistics M]
  exact PBRExclusion.Proofs.statistics_sum _ sA sB T

theorem sum_statistics (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) :
    ∑ y, M.statistics sA sB T xA xB y = M.A.marginal sA xA * M.B.marginal sB xB := by
  rw [← pairModel_statistics M, PBRExclusion.Proofs.sum_statistics, pairModel_marginal_A,
    pairModel_marginal_B]

theorem CE4_eq (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    CE4 M.statistics = 1 - F4 M.statistics / 4 := by
  rw [← pairModel_statistics M]
  exact PBRExclusion.Proofs.CE4_eq _ (pairModel_unbiased_A M hA) (pairModel_unbiased_B M hB)

theorem quarter_le_F4 (M : Model Λ Λ) (h : M.A = M.B) : 1 / 4 ≤ F4 M.statistics := by
  rw [← pairModel_statistics M]
  exact PBRExclusion.Proofs.quarter_le_F4 _ (pairModel_A_eq_B M h)

theorem CE4_le (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    CE4 M.statistics ≤ 15 / 16 := by
  rw [← pairModel_statistics M]
  exact PBRExclusion.Proofs.CE4_le _ (pairModel_A_eq_B M h) (pairModel_unbiased_A M hU)

end

end PBRExclusion.General.Proofs
