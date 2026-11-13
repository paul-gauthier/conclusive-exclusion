import PBRExclusion.Proofs.GeneralBound
import PBRExclusion.Proofs.OfFinite

/-!
# Statements for ontic states in any probability space

Each statement in this file is proved. What follows its `:=` is the name of the proof in
`PBRExclusion/Proofs/`, so the file can be read without the proofs.

The definitions are in `PBRExclusion/GeneralDefs.lean`. In this file `Source` and `Model` are the
ones with ontic states in any probability space, and `PBRExclusion.Source` and
`PBRExclusion.Model` are the finite ones of `PBRExclusion/Defs.lean`.
-/

namespace PBRExclusion.General

open MeasureTheory

noncomputable section

variable {Λ ΛA ΛB : Type*} [MeasurableSpace Λ] [MeasurableSpace ΛA] [MeasurableSpace ΛB]

/-! ## The statistics of a classical causal model -/

/-- The statistics of a classical causal model are nonnegative. -/
theorem Model.statistics_nonneg (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2)
    (y : Outcome) : 0 ≤ M.statistics sA sB T xA xB y := Proofs.statistics_nonneg M sA sB T xA xB y

/-- The statistics of a classical causal model are a probability distribution over the three
outcomes. -/
theorem Model.statistics_sum (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, M.statistics sA sB T xA xB y = 1 := Proofs.statistics_sum M sA sB T

/-- The two sources' outcomes are independent, and they depend on neither the other source's
setting nor the task. This sum is the denominator in `CE`. -/
theorem Model.sum_statistics (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) :
    ∑ y, M.statistics sA sB T xA xB y = M.A.marginal sA xA * M.B.marginal sB xB :=
  Proofs.sum_statistics M sA sB T xA xB

/-! ## Finite models as models of this kind -/

/-- A finite source has the same marginals as a source of this kind. -/
theorem Source.ofFinite_marginal [Fintype Λ] [MeasurableSingletonClass Λ]
    (S : PBRExclusion.Source Λ) (s x : Fin 2) : (Source.ofFinite S).marginal s x = S.marginal s x :=
  Proofs.ofFinite_marginal S s x

/-- A finite source has the same joint overlaps as a source of this kind. -/
theorem Source.ofFinite_jointOverlap [Fintype Λ] [MeasurableSingletonClass Λ]
    (S : PBRExclusion.Source Λ) (T : Task) :
    (Source.ofFinite S).jointOverlap T = S.jointOverlap T := Proofs.ofFinite_jointOverlap S T

/-- A finite model has the same statistics as a model of this kind. -/
theorem Model.ofFinite_statistics [Fintype ΛA] [Fintype ΛB] [MeasurableSingletonClass ΛA]
    [MeasurableSingletonClass ΛB] (M : PBRExclusion.Model ΛA ΛB) :
    (Model.ofFinite M).statistics = M.statistics := Proofs.ofFinite_statistics M

/-! ## The reduction to finite models -/

/-- Every classical causal model, with ontic states in any probability spaces, has the statistics
of a finite model whose ontic states are pairs of outcomes. The finite model's sources report
each outcome with the same probabilities. -/
theorem Model.exists_pair_model (M : Model ΛA ΛB) :
    ∃ N : PBRExclusion.Model Pair Pair, N.statistics = M.statistics ∧
      (∀ s x, N.A.marginal s x = M.A.marginal s x) ∧
      ∀ s x, N.B.marginal s x = M.B.marginal s x := Proofs.exists_pair_model M

/-- If the two sources of a classical causal model are independent copies of one source, the
finite model with its statistics can be taken with two independent copies of one source. -/
theorem Model.exists_pair_model_of_eq (M : Model Λ Λ) (h : M.A = M.B) :
    ∃ N : PBRExclusion.Model Pair Pair, N.A = N.B ∧ N.statistics = M.statistics ∧
      ∀ s x, N.A.marginal s x = M.A.marginal s x := Proofs.exists_pair_model_of_eq M h

/-! ## The steps of Appendix B, and the bound for one source -/

/-- On any source the four joint overlaps sum to at least one. -/
theorem Source.one_le_sum_jointOverlap (S : Source Λ) : 1 ≤ ∑ T : Task, S.jointOverlap T :=
  Proofs.one_le_sum_jointOverlap S

/-- In any classical causal model and any task, the forbidden mass is at least the product of the
two sources' joint overlaps. -/
theorem Model.jointOverlap_mul_le_forbidden (M : Model ΛA ΛB) (T : Task) :
    M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T :=
  Proofs.jointOverlap_mul_le_forbidden M T

/-- With unbiased outcomes, the paper's CE is `1 - F4 / 4`. -/
theorem Model.CE4_eq (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    CE4 M.statistics = 1 - F4 M.statistics / 4 := Proofs.CE4_eq M hA hB

/-- When the two sources are independent copies of one source, the four tasks have forbidden mass
at least one quarter. -/
theorem Model.quarter_le_F4 (M : Model Λ Λ) (h : M.A = M.B) : 1 / 4 ≤ F4 M.statistics :=
  Proofs.quarter_le_F4 M h

/-- When the two sources are independent copies of one source with unbiased outcomes, CE is at
most 15/16, whatever the joint measurement and whatever probability space the ontic state lives
in. -/
theorem Model.CE4_le (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    CE4 M.statistics ≤ 15 / 16 := Proofs.CE4_le M h hU

/-- The bound for two independent copies of one unbiased source is tight, and its hypotheses can
be met. -/
theorem exists_same_source_CE4_eq :
    ∃ M : Model Pair Pair, M.A = M.B ∧ M.A.Unbiased ∧ F4 M.statistics = 1 / 4 ∧
      CE4 M.statistics = 15 / 16 := Proofs.exists_same_source_CE4_eq

end

end PBRExclusion.General
