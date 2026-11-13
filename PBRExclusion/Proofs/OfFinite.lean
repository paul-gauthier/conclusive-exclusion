import PBRExclusion.Proofs.Examples
import PBRExclusion.Proofs.Reduction

/-!
# Proofs that finite models are models with ontic states in probability spaces

On a finite model the general marginal, joint overlap and statistics are the finite ones. So the
explicit models of `PBRExclusion/Defs.lean` are models with ontic states in probability spaces,
with the same statistics. The statements are in
`PBRExclusion/GeneralStatements.lean`.
-/

namespace PBRExclusion.General.Proofs

open MeasureTheory

noncomputable section

variable {Λ ΛA ΛB : Type*} [MeasurableSpace Λ] [MeasurableSpace ΛA] [MeasurableSpace ΛB]
  [Fintype Λ] [Fintype ΛA] [Fintype ΛB]
  [MeasurableSingletonClass Λ] [MeasurableSingletonClass ΛA] [MeasurableSingletonClass ΛB]

/-- An integral against a finite source's measure is the weighted sum. -/
theorem integral_ofFinite (S : PBRExclusion.Source Λ) (f : Λ → ℝ) :
    ∫ l, f l ∂(Source.ofFinite S).ν = ∑ l, S.p l * f l := by
  change ∫ l, f l ∂(∑ l, ENNReal.ofReal (S.p l) • Measure.dirac l) = _
  rw [integral_finsetSum_measure fun l _ =>
    (Integrable.of_finite : Integrable f (Measure.dirac l)).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (S.p_nonneg l), smul_eq_mul]

theorem ofFinite_marginal (S : PBRExclusion.Source Λ) (s x : Fin 2) :
    (Source.ofFinite S).marginal s x = S.marginal s x :=
  integral_ofFinite S fun l => S.resp s l x

theorem ofFinite_jointOverlap (S : PBRExclusion.Source Λ) (T : Task) :
    (Source.ofFinite S).jointOverlap T = S.jointOverlap T :=
  integral_ofFinite S fun l => min (S.resp 0 l (T 0)) (S.resp 1 l (T 1))

theorem ofFinite_unbiased (S : PBRExclusion.Source Λ) (h : S.Unbiased) : (Source.ofFinite
S).Unbiased :=
  fun s x => (ofFinite_marginal S s x).trans (h s x)

/-- This is Fubini's theorem for two sums of point masses. -/
theorem ofFinite_statistics (M : PBRExclusion.Model ΛA ΛB) :
    (Model.ofFinite M).statistics = M.statistics := by
  funext sA sB T xA xB y
  change ∫ l : ΛA × ΛB, M.A.resp sA l.1 xA * M.B.resp sB l.2 xB * M.ξ T l.1 l.2 y
    ∂((Source.ofFinite M.A).ν.prod (Source.ofFinite M.B).ν) = _
  rw [integral_prod _ Integrable.of_finite]
  simp only [integral_ofFinite, PBRExclusion.Model.statistics]
  refine Finset.sum_congr rfl fun lA _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun lB _ => ?_
  ring

/-! ## The explicit models with ontic states in probability spaces -/

theorem exists_same_source_CE4_eq :
    ∃ M : Model Pair Pair, M.A = M.B ∧ M.A.Unbiased ∧ F4 M.statistics = 1 / 4 ∧
      CE4 M.statistics = 15 / 16 :=
  ⟨Model.ofFinite toy, rfl, ofFinite_unbiased _ PBRExclusion.Proofs.toyBit_unbiased, by
    rw [ofFinite_statistics]
    exact PBRExclusion.Proofs.toy_F4, by
    rw [ofFinite_statistics]
    exact PBRExclusion.Proofs.toy_CE4⟩

end

end PBRExclusion.General.Proofs
