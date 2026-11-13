import PBRExclusion.Proofs.Reduction

/-!
# Proofs for the joint overlaps in any probability space

On a source the four joint overlaps sum to at least one, and a task's forbidden mass is at least the
product of the two sources' joint overlaps. These are the two lemmas of
`PBRExclusion/Proofs/Bound.lean` with integrals for sums. The statements are in
`PBRExclusion/GeneralStatements.lean`.
-/

namespace PBRExclusion.General.Proofs

open MeasureTheory

noncomputable section

variable {Λ ΛA ΛB : Type*} [MeasurableSpace Λ] [MeasurableSpace ΛA] [MeasurableSpace ΛB]

/-! ## One source -/

/-- The integrand of the joint overlap, which is the smaller of the two responses that the task
picks. -/
def minResp (S : Source Λ) (T : Task) (l : Λ) : ℝ := min (S.resp 0 l (T 0)) (S.resp 1 l (T 1))

theorem minResp_nonneg (S : Source Λ) (T : Task) (l : Λ) : 0 ≤ minResp S T l :=
  le_min (S.resp_nonneg _ _ _) (S.resp_nonneg _ _ _)

theorem minResp_le_one (S : Source Λ) (T : Task) (l : Λ) : minResp S T l ≤ 1 :=
  (min_le_left _ _).trans (resp_le_one S _ _ _)

theorem measurable_minResp (S : Source Λ) (T : Task) : Measurable (minResp S T) :=
  (S.resp_measurable 0 (T 0)).min (S.resp_measurable 1 (T 1))

theorem integrable_minResp (S : Source Λ) (T : Task) : Integrable (minResp S T) S.ν :=
  integrable_of_unit (measurable_minResp S T) (minResp_nonneg S T) (minResp_le_one S T)

/-- The smaller of two numbers between 0 and 1 is at least their product. -/
theorem weight_le_minResp (S : Source Λ) (T : Task) (l : Λ) : weight S T l ≤ minResp S T l :=
  le_min (mul_le_of_le_one_right (S.resp_nonneg _ _ _) (resp_le_one S _ _ _))
    (mul_le_of_le_one_left (S.resp_nonneg _ _ _) (resp_le_one S _ _ _))

/-- At each ontic state the four weights sum to one, and each is at most the smaller response. -/
theorem one_le_sum_jointOverlap (S : Source Λ) : 1 ≤ ∑ T : Task, S.jointOverlap T := by
  have h : ∑ T : Task, S.jointOverlap T = ∫ l, ∑ T : Task, minResp S T l ∂S.ν :=
    (integral_finsetSum _ fun T _ => integrable_minResp S T).symm
  rw [h]
  calc (1 : ℝ) = ∫ _l, (1 : ℝ) ∂S.ν := by simp
    _ ≤ ∫ l, ∑ T : Task, minResp S T l ∂S.ν :=
        integral_mono (integrable_const 1)
          (integrable_finsetSum _ fun T _ => integrable_minResp S T) fun l => by
            rw [← sum_weight S l]
            exact Finset.sum_le_sum fun T _ => weight_le_minResp S T l

/-! ## One task -/

theorem jointOverlap_mul_le_forbidden (M : Model ΛA ΛB) (T : Task) :
    M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T := by
  have hint : ∀ i j : Fin 2, Integrable (fun l : ΛA × ΛB =>
      M.A.resp i l.1 (T i) * M.B.resp j l.2 (T j) * M.ξ T l.1 l.2 (i, j))
      (M.A.ν.prod M.B.ν) := fun i j =>
    integrable_of_unit
      ((((M.A.resp_measurable i (T i)).comp measurable_fst).mul
        ((M.B.resp_measurable j (T j)).comp measurable_snd)).mul (M.ξ_measurable T (i, j)))
      (fun l => mul_nonneg (mul_nonneg (M.A.resp_nonneg _ _ _) (M.B.resp_nonneg _ _ _))
        (M.ξ_nonneg _ _ _ _))
      (fun l => mul_le_one_of_unit
        (mul_le_one_of_unit (resp_le_one _ _ _ _) (M.B.resp_nonneg _ _ _) (resp_le_one _ _ _ _))
        (M.ξ_nonneg _ _ _ _) (ξ_le_one M _ _ _ _))
  have hmin : Integrable (fun l : ΛA × ΛB => minResp M.A T l.1 * minResp M.B T l.2)
      (M.A.ν.prod M.B.ν) :=
    integrable_of_unit
      (((measurable_minResp M.A T).comp measurable_fst).mul
        ((measurable_minResp M.B T).comp measurable_snd))
      (fun l => mul_nonneg (minResp_nonneg _ _ _) (minResp_nonneg _ _ _))
      (fun l => mul_le_one_of_unit (minResp_le_one _ _ _) (minResp_nonneg _ _ _)
        (minResp_le_one _ _ _))
  calc M.A.jointOverlap T * M.B.jointOverlap T
      = ∫ l, minResp M.A T l.1 * minResp M.B T l.2 ∂(M.A.ν.prod M.B.ν) :=
        (integral_prod_mul (minResp M.A T) (minResp M.B T)).symm
    _ ≤ ∫ l, ∑ i, ∑ j, M.A.resp i l.1 (T i) * M.B.resp j l.2 (T j) *
          M.ξ T l.1 l.2 (i, j) ∂(M.A.ν.prod M.B.ν) :=
        integral_mono hmin
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j)
          fun l => by
            have h1 : ∑ i, ∑ j, M.ξ T l.1 l.2 (i, j) = 1 := by
              rw [← M.ξ_sum T l.1 l.2, Fintype.sum_prod_type]
            calc minResp M.A T l.1 * minResp M.B T l.2
                = ∑ i, ∑ j, minResp M.A T l.1 * minResp M.B T l.2 *
                    M.ξ T l.1 l.2 (i, j) := by
                  simp_rw [← Finset.mul_sum, h1, mul_one]
              _ ≤ ∑ i, ∑ j, M.A.resp i l.1 (T i) * M.B.resp j l.2 (T j) *
                    M.ξ T l.1 l.2 (i, j) :=
                  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul
                        (PBRExclusion.Proofs.min_le_apply (fun i l => M.A.resp i l (T i)) i l.1)
                        (PBRExclusion.Proofs.min_le_apply (fun j l => M.B.resp j l (T j)) j l.2)
                        (minResp_nonneg _ _ _) (M.A.resp_nonneg _ _ _))
                      (M.ξ_nonneg _ _ _ _)
    _ = forbidden M.statistics T := by
        simp only [forbidden, Model.statistics]
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]

end

end PBRExclusion.General.Proofs
