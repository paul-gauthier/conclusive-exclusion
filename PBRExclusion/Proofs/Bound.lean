import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import PBRExclusion.Defs

/-!
# Proofs of the bound for finite ontic state spaces

The statements are in `PBRExclusion/Statements.lean`.

The argument has three steps.

1. Each task's forbidden mass is at least the product of the two sources' joint overlaps
   (`jointOverlap_mul_le_forbidden`).
2. On each source the four joint overlaps sum to at least one (`one_le_sum_jointOverlap`), by a
   pointwise identity (`sum_min_eq_add_two_mul_min`).
3. Over the paper's four tasks, with equal joint overlaps on the two sources, the forbidden mass is
   at least a quarter (`quarter_le_F4_of_jointOverlap_eq`).

Steps 1 and 2 are proved once, for plain nonnegative weights (`sum_min_mul_sum_min_le` and
`sum_le_sum_min`), so that the form with sources and Appendix B's own form both follow from them.
-/

namespace PBRExclusion.Proofs

noncomputable section

variable {Λ ΛA ΛB : Type*} [Fintype Λ] [Fintype ΛA] [Fintype ΛB]

/-! ## Sums -/

/-- Four nested sums can have the outer two moved inside. -/
theorem sum_comm₄ {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d :=
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- There are four pairs. -/
theorem sum_pair_one : ∑ _τ : Pair, (1 : ℝ) = 4 := by
  rw [sum_pair]; norm_num

/-- The Cauchy-Schwarz inequality over the four tasks, which is the paper's step (B17). -/
theorem sq_sum_le_four_mul_sum_sq (g : Pair → ℝ) : (∑ T, g T) ^ 2 ≤ 4 * ∑ T, g T ^ 2 := by
  rw [sum_pair, sum_pair]
  nlinarith [sq_nonneg (g ![0, 0] - g ![0, 1]), sq_nonneg (g ![0, 0] - g ![1, 0]),
    sq_nonneg (g ![0, 0] - g ![1, 1]), sq_nonneg (g ![0, 1] - g ![1, 0]),
    sq_nonneg (g ![0, 1] - g ![1, 1]), sq_nonneg (g ![1, 0] - g ![1, 1])]

/-! ## The statistics are a probability distribution -/

theorem statistics_nonneg (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2)
    (y : Outcome) : 0 ≤ M.statistics sA sB T xA xB y :=
  Finset.sum_nonneg fun lA _ => Finset.sum_nonneg fun lB _ =>
    mul_nonneg (mul_nonneg (M.A.p_nonneg lA) (M.B.p_nonneg lB))
      (mul_nonneg (mul_nonneg (M.A.resp_nonneg sA lA xA) (M.B.resp_nonneg sB lB xB))
        (M.ξ_nonneg T lA lB y))

theorem marginal_nonneg (S : Source Λ) (s x : Fin 2) : 0 ≤ S.marginal s x :=
  Finset.sum_nonneg fun l _ => mul_nonneg (S.p_nonneg l) (S.resp_nonneg s l x)

/-- A source's outcomes have total probability one under each setting. -/
theorem sum_marginal (S : Source Λ) (s : Fin 2) : ∑ x, S.marginal s x = 1 := by
  unfold Source.marginal
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, S.resp_sum, mul_one]
  exact S.p_sum

theorem sum_statistics (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) :
    ∑ y, M.statistics sA sB T xA xB y = M.A.marginal sA xA * M.B.marginal sB xB := by
  simp only [Model.statistics, Source.marginal]
  rw [Finset.sum_comm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun lA _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lB _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, M.ξ_sum]
  ring

theorem statistics_sum (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, M.statistics sA sB T xA xB y = 1 := by
  simp_rw [sum_statistics]
  rw [← Finset.sum_mul_sum, sum_marginal, sum_marginal, mul_one]

/-! ## The joint overlaps of one source -/

theorem sum_min_eq_add_two_mul_min {a₀ a₁ b₀ b₁ : ℝ} (h : a₀ + a₁ = b₀ + b₁) :
    min a₀ b₀ + min a₀ b₁ + min a₁ b₀ + min a₁ b₁ = a₀ + a₁ + 2 * min (min a₀ a₁) (min b₀ b₁) := by
  simp only [min_def]
  split_ifs <;> linarith

/-- The sum of the joint overlaps, for plain weights. `f s x l` is the weight of the ontic state `l`
under the label `(s, x)`. If the two settings give every ontic state the same total weight, the four
joint overlaps sum to at least that total. This is `sum_min_eq_add_two_mul_min` at every ontic
state. -/
theorem sum_le_sum_min (f : Fin 2 → Fin 2 → Λ → ℝ) (hf : ∀ s x l, 0 ≤ f s x l)
    (h : ∀ l, f 0 0 l + f 0 1 l = f 1 0 l + f 1 1 l) :
    ∑ l, (f 0 0 l + f 0 1 l) ≤ ∑ T : Task, ∑ l, min (f 0 (T 0) l) (f 1 (T 1) l) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [sum_pair]
  have key := sum_min_eq_add_two_mul_min (h l)
  have hmin : 0 ≤ min (min (f 0 0 l) (f 0 1 l)) (min (f 1 0 l) (f 1 1 l)) :=
    le_min (le_min (hf _ _ _) (hf _ _ _)) (le_min (hf _ _ _) (hf _ _ _))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-- The joint overlap, with the ontic state's probability moved inside the minimum. -/
theorem jointOverlap_eq (S : Source Λ) (T : Task) :
    S.jointOverlap T = ∑ l, min (S.p l * S.resp 0 l (T 0)) (S.p l * S.resp 1 l (T 1)) :=
  Finset.sum_congr rfl fun l _ => mul_min_of_nonneg _ _ (S.p_nonneg l)

theorem one_le_sum_jointOverlap (S : Source Λ) : 1 ≤ ∑ T : Task, S.jointOverlap T := by
  have hr : ∀ s l, S.resp s l 0 + S.resp s l 1 = 1 := fun s l => by
    simpa [Fin.sum_univ_two] using S.resp_sum s l
  have h := sum_le_sum_min (fun s x l => S.p l * S.resp s l x)
    (fun s x l => mul_nonneg (S.p_nonneg l) (S.resp_nonneg s l x))
    (fun l => by simp only [← mul_add, hr])
  have hs : ∑ l, (S.p l * S.resp 0 l 0 + S.p l * S.resp 0 l 1) = 1 := by
    simp only [← mul_add, hr, mul_one]
    exact S.p_sum
  simp only [jointOverlap_eq]
  linarith

/-! ## One task -/

/-- The smaller of two weights is at most either. -/
theorem min_le_apply {Λ' : Type*} (f : Fin 2 → Λ' → ℝ) (i : Fin 2) (l : Λ') :
    min (f 0 l) (f 1 l) ≤ f i l := by
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- The product bound, for plain weights. `fA i l` is the weight that source A gives the ontic state
`l` when the task's state under the setting `i` is prepared, and `fB` likewise. Whatever the
response function, the weight on the excluded states is at least the product of the two joint
overlaps. This is the paper's (B8). -/
theorem sum_min_mul_sum_min_le (fA : Fin 2 → ΛA → ℝ) (fB : Fin 2 → ΛB → ℝ)
    (c : ΛA → ΛB → Outcome → ℝ) (hA : ∀ i l, 0 ≤ fA i l) (hB : ∀ j l, 0 ≤ fB j l)
    (hc : ∀ lA lB y, 0 ≤ c lA lB y) (hc1 : ∀ lA lB, ∑ y, c lA lB y = 1) :
    (∑ lA, min (fA 0 lA) (fA 1 lA)) * (∑ lB, min (fB 0 lB) (fB 1 lB)) ≤
      ∑ i, ∑ j, ∑ lA, ∑ lB, fA i lA * fB j lB * c lA lB (i, j) := by
  calc (∑ lA, min (fA 0 lA) (fA 1 lA)) * (∑ lB, min (fB 0 lB) (fB 1 lB))
      = ∑ lA, ∑ lB, min (fA 0 lA) (fA 1 lA) * min (fB 0 lB) (fB 1 lB) :=
        Finset.sum_mul_sum _ _ _ _
    _ = ∑ lA, ∑ lB, ∑ i, ∑ j,
          min (fA 0 lA) (fA 1 lA) * min (fB 0 lB) (fB 1 lB) * c lA lB (i, j) := by
        refine Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
        have h1 : ∑ i, ∑ j, c lA lB (i, j) = 1 := by
          rw [← hc1 lA lB, Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, h1, mul_one]
    _ ≤ ∑ lA, ∑ lB, ∑ i, ∑ j, fA i lA * fB j lB * c lA lB (i, j) := by
        refine Finset.sum_le_sum fun lA _ => Finset.sum_le_sum fun lB _ =>
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (min_le_apply fA i lA) (min_le_apply fB j lB)
            (le_min (hB 0 lB) (hB 1 lB)) (hA i lA))
          (hc lA lB (i, j))
    _ = ∑ i, ∑ j, ∑ lA, ∑ lB, fA i lA * fB j lB * c lA lB (i, j) := sum_comm₄ _

theorem jointOverlap_mul_le_forbidden (M : Model ΛA ΛB) (T : Task) :
    M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T := by
  have h := sum_min_mul_sum_min_le (fun i l => M.A.p l * M.A.resp i l (T i))
    (fun j l => M.B.p l * M.B.resp j l (T j)) (M.ξ T)
    (fun i l => mul_nonneg (M.A.p_nonneg l) (M.A.resp_nonneg i l _))
    (fun j l => mul_nonneg (M.B.p_nonneg l) (M.B.resp_nonneg j l _))
    (M.ξ_nonneg T) (M.ξ_sum T)
  rw [jointOverlap_eq, jointOverlap_eq]
  refine h.trans (le_of_eq ?_)
  simp only [forbidden, Model.statistics]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
  ring

/-! ## The paper's CE with unbiased outcomes -/

/-- With unbiased outcomes each of a task's four states has probability one quarter, so the paper's
`CE_T` is one minus the forbidden mass of the task. -/
theorem CE_eq_of_unbiased (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    CE M.statistics T = 1 - forbidden M.statistics T := by
  unfold CE forbidden
  simp_rw [sum_statistics, hA _ _, hB _ _]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem CE4_eq (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    CE4 M.statistics = 1 - F4 M.statistics / 4 := by
  unfold CE4 F4
  simp_rw [CE_eq_of_unbiased M hA hB]
  rw [Finset.sum_sub_distrib, sum_pair_one]
  ring

/-! ## The paper's four tasks -/

/-- The bound under the hypothesis that its proof uses, which is that the two sources have equal
joint overlaps. The sources may have different ontic state spaces, and one source for both qubits is
a special case. -/
theorem quarter_le_F4_of_jointOverlap_eq (M : Model ΛA ΛB)
    (h : ∀ T, M.A.jointOverlap T = M.B.jointOverlap T) : 1 / 4 ≤ F4 M.statistics := by
  have h1 := one_le_sum_jointOverlap M.A
  have h2 := sq_sum_le_four_mul_sum_sq M.A.jointOverlap
  have h3 : ∑ T : Task, M.A.jointOverlap T ^ 2 ≤ F4 M.statistics := by
    unfold F4
    refine Finset.sum_le_sum fun T _ => ?_
    have h4 : M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T :=
      jointOverlap_mul_le_forbidden M T
    rw [← h T] at h4
    rwa [sq]
  nlinarith [sq_nonneg ((∑ T : Task, M.A.jointOverlap T) - 1)]

theorem quarter_le_F4 (M : Model Λ Λ) (h : M.A = M.B) : 1 / 4 ≤ F4 M.statistics :=
  quarter_le_F4_of_jointOverlap_eq M fun T => by rw [h]

theorem CE4_le (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    CE4 M.statistics ≤ 15 / 16 := by
  rw [CE4_eq M hU (h ▸ hU)]
  linarith [quarter_le_F4 M h]

/-! ## The paper's `β` -/

theorem β_eq_two_mul_jointOverlap (S : Source Λ) (h : S.Unbiased) (T : Task) :
    S.β T = 2 * S.jointOverlap T := by
  simp only [Source.β, Source.μ, Source.jointOverlap, h _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show S.p l * S.resp 0 l (T 0) / (1 / 2) = 2 * (S.p l * S.resp 0 l (T 0)) by ring,
    show S.p l * S.resp 1 l (T 1) / (1 / 2) = 2 * (S.p l * S.resp 1 l (T 1)) by ring,
    ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← mul_min_of_nonneg _ _ (S.p_nonneg l)]

theorem CE_le_β (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    CE M.statistics T ≤ 1 - 1 / 4 * (M.A.β T * M.B.β T) := by
  rw [CE_eq_of_unbiased M hA hB, β_eq_two_mul_jointOverlap _ hA, β_eq_two_mul_jointOverlap _ hB]
  have := jointOverlap_mul_le_forbidden M T
  linarith

end

end PBRExclusion.Proofs
