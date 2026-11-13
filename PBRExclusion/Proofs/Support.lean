import PBRExclusion.NetworkStatements
import PBRExclusion.Statements

/-!
# Proofs for the two-bit model and the support of the quantum statistics

The statements are in `PBRExclusion/SupportStatements.lean`.

The gap is proved for a fixed task. Call a pair of ontic states live when both have positive
probability.

* When an event has probability zero, every term of its sum is zero (`term_eq_zero`). So at a live
  pair, whenever the sources can give two outcomes, the measurement never gives the impossible
  outcome of that product state (`ξ_impossibleOutcome`).
* If the outcomes that a live pair can give under the two settings have the same parity on both
  sources, the four impossible outcomes are all four outcomes (`impossibleOutcome_cover`). The
  response function would then give every outcome probability zero, which it cannot
  (`parity_ne`).
* A live pair that gives the state `|0⟩|0⟩` the outcome `Y2` has a source A that reports 0 under
  both settings. One that gives it the outcome `Y3` has a source B that reports 0 under both.
  Together they are a live pair with equal parities.
-/

namespace PBRExclusion.Support.Proofs

open MeasureTheory

noncomputable section

/-! ## The rule -/

theorem impossibleOutcome_eq (sA xA sB xB : Fin 2) :
    impossibleOutcome sA xA sB xB = if xA = xB then (sA, sB) else (sA + 1, sB + 1) := by
  revert sA xA sB xB
  decide

/-- If the outcomes under the two settings have the same parity on both sources, the four impossible
outcomes are all four outcomes. -/
theorem impossibleOutcome_cover {a0 a1 b0 b1 : Fin 2} (h : a0 + a1 = b0 + b1) (y : Outcome) :
    y = impossibleOutcome 0 a0 0 b0 ∨ y = impossibleOutcome 0 a0 1 b1 ∨
      y = impossibleOutcome 1 a1 0 b0 ∨
      y = impossibleOutcome 1 a1 1 b1 := by
  revert a0 a1 b0 b1 y
  decide

/-! ## Classical causal models with finite ontic state spaces -/

section Finite

variable {Λ ΛA ΛB : Type*} [Fintype Λ] [Fintype ΛA] [Fintype ΛB]

theorem term_nonneg (M : Model ΛA ΛB) (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) (y : Outcome)
    (lA : ΛA) (lB : ΛB) :
    0 ≤ M.A.p lA * M.B.p lB * (M.A.resp sA lA xA * M.B.resp sB lB xB * M.ξ T lA lB y) :=
  mul_nonneg (mul_nonneg (M.A.p_nonneg _) (M.B.p_nonneg _))
    (mul_nonneg (mul_nonneg (M.A.resp_nonneg _ _ _) (M.B.resp_nonneg _ _ _))
      (M.ξ_nonneg _ _ _ _))

/-- When an event has probability zero, every term of its sum is zero. -/
theorem term_eq_zero (M : Model ΛA ΛB) {sA sB : Fin 2} {T : Task} {xA xB : Fin 2} {y : Outcome}
    (h : M.statistics sA sB T xA xB y = 0) (lA : ΛA) (lB : ΛB) :
    M.A.p lA * M.B.p lB * (M.A.resp sA lA xA * M.B.resp sB lB xB * M.ξ T lA lB y) = 0 := by
  unfold Model.statistics at h
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun lA _ =>
    Finset.sum_nonneg fun lB _ => term_nonneg M sA sB T xA xB y lA lB).1 h lA (Finset.mem_univ _)
  exact (Finset.sum_eq_zero_iff_of_nonneg fun lB _ =>
    term_nonneg M sA sB T xA xB y lA lB).1 h1 lB (Finset.mem_univ _)

/-- An event of positive probability has a live pair of ontic states that gives it. -/
theorem exists_term_pos (M : Model ΛA ΛB) {sA sB : Fin 2} {T : Task} {xA xB : Fin 2}
    {y : Outcome} (h : M.statistics sA sB T xA xB y ≠ 0) :
    ∃ lA lB, 0 < M.A.p lA ∧ 0 < M.B.p lB ∧ 0 < M.A.resp sA lA xA ∧ 0 < M.B.resp sB lB xB ∧
      0 < M.ξ T lA lB y := by
  unfold Model.statistics at h
  obtain ⟨lA, -, hA⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨lB, -, hB⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  refine ⟨lA, lB, ?_⟩
  simp only [mul_ne_zero_iff] at hB
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hB
  exact ⟨lt_of_le_of_ne (M.A.p_nonneg _) (Ne.symm h1), lt_of_le_of_ne (M.B.p_nonneg _) (Ne.symm h2),
    lt_of_le_of_ne (M.A.resp_nonneg _ _ _) (Ne.symm h3),
    lt_of_le_of_ne (M.B.resp_nonneg _ _ _) (Ne.symm h4),
    lt_of_le_of_ne (M.ξ_nonneg _ _ _ _) (Ne.symm h5)⟩

/-- Each ontic state can give some outcome under each setting. -/
theorem exists_resp_pos (S : Source Λ) (s : Fin 2) (l : Λ) : ∃ x, 0 < S.resp s l x := by
  by_contra h
  push Not at h
  have h0 : ∑ x, S.resp s l x ≤ 0 := Finset.sum_nonpos fun x _ => h x
  linarith [S.resp_sum s l]

/-- At a live pair, whenever the sources can give two outcomes, the joint measurement never gives
the impossible outcome of that product state. -/
theorem ξ_impossibleOutcome (M : Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0)
    {lA : ΛA} {lB : ΛB}
    (hA : 0 < M.A.p lA) (hB : 0 < M.B.p lB) {sA xA sB xB : Fin 2}
    (ha : 0 < M.A.resp sA lA xA) (hb : 0 < M.B.resp sB lB xB) :
    M.ξ T lA lB (impossibleOutcome sA xA sB xB) = 0 := by
  have h0 := term_eq_zero M (h sA xA sB xB) lA lB
  simp only [mul_eq_zero] at h0
  rcases h0 with (h1 | h1) | (h1 | h1) | h1
  · exact absurd h1 hA.ne'
  · exact absurd h1 hB.ne'
  · exact absurd h1 ha.ne'
  · exact absurd h1 hb.ne'
  · exact h1

/-- At a live pair, the outcomes that the two sources can give under the two settings have different
parities. -/
theorem parity_ne (M : Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0)
    {lA : ΛA} {lB : ΛB}
    (hA : 0 < M.A.p lA) (hB : 0 < M.B.p lB) {a0 a1 b0 b1 : Fin 2}
    (ha0 : 0 < M.A.resp 0 lA a0) (ha1 : 0 < M.A.resp 1 lA a1)
    (hb0 : 0 < M.B.resp 0 lB b0) (hb1 : 0 < M.B.resp 1 lB b1) : a0 + a1 ≠ b0 + b1 := by
  intro heq
  have hz : ∀ y, M.ξ T lA lB y = 0 := by
    intro y
    rcases impossibleOutcome_cover heq y with rfl | rfl | rfl | rfl
    · exact ξ_impossibleOutcome M T h hA hB ha0 hb0
    · exact ξ_impossibleOutcome M T h hA hB ha0 hb1
    · exact ξ_impossibleOutcome M T h hA hB ha1 hb0
    · exact ξ_impossibleOutcome M T h hA hB ha1 hb1
  have hsum := M.ξ_sum T lA lB
  simp [hz] at hsum

theorem not_both_finite (M : Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0) :
    M.statistics 0 0 T 0 0 (0, 1) = 0 ∨ M.statistics 0 0 T 0 0 (1, 0) = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨h2, h3⟩ := hne
  obtain ⟨lA, lB, hA, hB, ha, hb, hc⟩ := exists_term_pos M h2
  obtain ⟨lA', lB', hA', hB', ha', hb', hc'⟩ := exists_term_pos M h3
  obtain ⟨a1, ha1⟩ := exists_resp_pos M.A 1 lA
  obtain ⟨b1', hb1'⟩ := exists_resp_pos M.B 1 lB'
  have key : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  rcases key a1 with rfl | rfl
  · rcases key b1' with rfl | rfl
    · -- `lA` reports 0, 0 and `lB'` reports 0, 0, so a live pair has equal parities
      exact parity_ne M T h hA hB' ha ha1 hb' hb1' rfl
    · -- `lB'` can report 1 under the setting 1, and the impossible outcome of `|0⟩|-⟩` is `Y3`
      have h0 : M.ξ T lA' lB' (impossibleOutcome 0 0 1 1) = 0 :=
        ξ_impossibleOutcome M T h hA' hB' ha' hb1'
      exact hc'.ne' h0
  · -- `lA` can report 1 under the setting 1, and the impossible outcome of `|-⟩|0⟩` is `Y2`
    have h0 : M.ξ T lA lB (impossibleOutcome 1 1 0 0) = 0 := ξ_impossibleOutcome M T h hA hB ha1 hb
    exact hc.ne' h0

end Finite

/-! ## The two bits without the renaming -/

/-- `twoBitsRaw` has the sources of the two-bit model and a measurement that ignores the task. It
gives the outcome `(lA + lB, lA + lB + 1)` whatever the task. It is an auxiliary model for the
proofs below, and the model `twoBits` renames its outcome as the task does. -/
def twoBitsRaw : Model (Fin 2) (Fin 2) where
  A := bitSame.toSource
  B := bitFlip.toSource
  ξ _ lA lB y := if (lA + lB, lA + lB + 1) = y then 1 else 0
  ξ_nonneg _ _ _ _ := by split_ifs <;> norm_num
  ξ_sum _ _ _ := by simp

theorem twoBitsRaw_impossibleOutcome (T : Task) (sA xA sB xB : Fin 2) :
    twoBitsRaw.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0 := by
  fin_cases sA <;> fin_cases xA <;> fin_cases sB <;> fin_cases xB <;>
    simp [Model.statistics, twoBitsRaw, DetSource.toSource, bitSame, bitFlip, impossibleOutcome,
      Fin.sum_univ_two]

theorem twoBitsRaw_state00 (T : Task) :
    twoBitsRaw.statistics 0 0 T 0 0 (0, 1) = 1 / 4 ∧
      twoBitsRaw.statistics 0 0 T 0 0 (1, 0) = 0 := by
  constructor
  · simp [Model.statistics, twoBitsRaw, DetSource.toSource, bitSame, bitFlip, Fin.sum_univ_two]
    norm_num
  · simp [Model.statistics, twoBitsRaw, DetSource.toSource, bitSame, bitFlip, Fin.sum_univ_two]

/-! ## Classical causal models with ontic states in any probability spaces -/

section General

variable {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB]

theorem not_both (M : General.Model ΛA ΛB) (T : Task)
    (h : ∀ sA xA sB xB, M.statistics sA sB T xA xB (impossibleOutcome sA xA sB xB) = 0) :
    M.statistics 0 0 T 0 0 (0, 1) = 0 ∨ M.statistics 0 0 T 0 0 (1, 0) = 0 := by
  obtain ⟨N, hN, -, -⟩ := General.Model.exists_pair_model M
  rw [← hN] at h ⊢
  exact not_both_finite N T h

end General

/-! ## The quantum side -/

theorem quantum_eq_zero_iff (T : Task) (sA sB xA xB : Fin 2) (y : Outcome) :
    Quantum.statistics sA sB T xA xB y = 0 ↔ relabel T y = impossibleOutcome sA xA sB xB := by
  rw [Quantum.statistics, Quantum.effect_eq_pbr, impossibleOutcome,
    ← Quantum.Proofs.born_pbr_eq_zero_iff]
  constructor
  · intro h0
    simpa using h0
  · intro h0
    rw [h0, mul_zero]

theorem quantum_state00 :
    Quantum.statistics 0 0 ![0, 0] 0 0 (0, 1) = 1 / 16 ∧
      Quantum.statistics 0 0 ![0, 0] 0 0 (1, 0) = 1 / 16 := by
  constructor <;>
  · rw [Quantum.statistics, Quantum.effect_eq_pbr, Quantum.pbr, Quantum.state,
      Quantum.Proofs.born_proj]
    simp [relabel, Quantum.pbrKet, Quantum.tensor, Quantum.ket, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-! ## The support of the quantum statistics -/

section Gap

variable {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB]

theorem zeroPlus_not_classical :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ sA sB xA xB y,
      (M.statistics sA sB ![0, 0] xA xB y = 0 ↔
        Quantum.statistics sA sB ![0, 0] xA xB y = 0) := by
  rintro ⟨M, hM⟩
  have hz : ∀ sA xA sB xB,
      M.statistics sA sB ![0, 0] xA xB (impossibleOutcome sA xA sB xB) = 0 := by
    intro sA xA sB xB
    refine (hM sA sB xA xB _).2 ((quantum_eq_zero_iff ![0, 0] sA sB xA xB _).2 ?_)
    simp [relabel]
  rcases not_both M _ hz with h2 | h3
  · have h := (hM 0 0 0 0 (0, 1)).1 h2
    rw [quantum_state00.1] at h
    norm_num at h
  · have h := (hM 0 0 0 0 (1, 0)).1 h3
    rw [quantum_state00.2] at h
    norm_num at h

theorem support_not_classical :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ T sA sB xA xB y,
      (M.statistics sA sB T xA xB y = 0 ↔ Quantum.statistics sA sB T xA xB y = 0) := by
  rintro ⟨M, hM⟩
  exact zeroPlus_not_classical ⟨M, hM ![0, 0]⟩

theorem bellModel_not_classical :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ T sA sB xA xB y,
      (M.statistics sA sB T xA xB y = 0 ↔
        Quantum.bellModel.statistics sA sB T xA xB y = 0) := by
  rw [Quantum.bellModel_statistics]
  exact support_not_classical

end Gap

/-! ## The impossible events of the quantum statistics in the two-bit model

The model `twoBits` of `PBRExclusion/Defs.lean` has the sources of `twoBitsRaw`, and its
measurement gives what the measurement of `twoBitsRaw` gives, renamed as the task renames. Renaming
twice changes nothing, so in the task `T` it gives the outcome `relabel T z` exactly when
`twoBitsRaw` gives `z` (`twoBits_statistics`). An impossible event of the quantum statistics has
an outcome `y` with `relabel T y = impossibleOutcome …` (`quantum_eq_zero_iff`), and `twoBitsRaw`
gives the outcome `impossibleOutcome …` probability zero (`twoBitsRaw_impossibleOutcome`). -/

/-- In the task `T` the two-bit model gives the outcome `relabel T z` exactly when
`twoBitsRaw` gives `z`. -/
theorem twoBits_statistics (T : Task) (sA sB xA xB : Fin 2) (z : Outcome) :
    twoBits.statistics sA sB T xA xB (relabel T z) =
      twoBitsRaw.statistics sA sB T xA xB z := by
  have hinj : ∀ w : Outcome, relabel T w = relabel T z ↔ w = z := fun w =>
    ⟨fun h => by simpa [Quantum.relabel_relabel] using congrArg (relabel T) h,
      fun h => by rw [h]⟩
  simp only [Model.statistics, twoBits, twoBitsRaw, hinj]

/-- Every impossible event of the quantum statistics is an impossible event of the two-bit model. -/
theorem twoBits_keeps (T : Task) (sA sB xA xB : Fin 2) (y : Outcome)
    (h : Quantum.statistics sA sB T xA xB y = 0) :
    twoBits.statistics sA sB T xA xB y = 0 := by
  rw [quantum_eq_zero_iff] at h
  have hy : y = relabel T (impossibleOutcome sA xA sB xB) := by rw [← h, Quantum.relabel_relabel]
  rw [hy, twoBits_statistics]
  exact twoBitsRaw_impossibleOutcome _ sA xA sB xB

/-! ## The two-bit model has CE = 1

In each task the measurement follows one rule, renamed as the task renames (`twoBits_ξ`). The four
events that a task's forbidden mass counts are impossible events of the quantum statistics
(`Quantum.Proofs.statistics_forbidden`), and each of those is impossible in the model
(`twoBits_keeps`), so the model has no forbidden mass in any task (`twoBits_forbidden`). Its
outcomes are unbiased, so its CE is `1 - forbidden = 1` in each task (`twoBits_CE`). -/

theorem twoBits_unbiased : twoBits.A.Unbiased ∧ twoBits.B.Unbiased :=
  ⟨bitSame_unbiased, bitFlip_unbiased⟩

/-- In the task `T` the measurement gives the outcome `relabel T z` exactly when `z` is
`(lA + lB, lA + lB + 1)`. -/
theorem twoBits_ξ (T : Task) (lA lB : Fin 2) (z : Outcome) :
    twoBits.ξ T lA lB (relabel T z) =
      if (lA + lB, lA + lB + 1) = z then 1 else 0 := by
  have hinj : ∀ w : Outcome, relabel T w = relabel T z ↔ w = z := fun w =>
    ⟨fun h => by simpa [Quantum.relabel_relabel] using congrArg (relabel T) h,
      fun h => by rw [h]⟩
  simp only [twoBits, hinj]

/-- This is the same rule with the renaming written out. -/
theorem twoBits_ξ_eq (T : Task) (lA lB : Fin 2) (y : Outcome) :
    twoBits.ξ T lA lB y =
      if y = (lA + lB + T 0 + T 1, lA + lB + T 0 + T 1 + 1) then 1 else 0 := by
  have key : ∀ a b lA lB : Fin 2, ∀ y : Outcome,
      (if a = b then ((lA + lB, lA + lB + 1) : Outcome)
        else ((lA + lB, lA + lB + 1) : Outcome).swap) = y ↔
        y = (lA + lB + a + b, lA + lB + a + b + 1) := by decide
  simp only [twoBits, relabel, key (T 0) (T 1) lA lB y]

/-- Each event that the forbidden mass counts is an impossible event of the quantum statistics, and
so of the model. -/
theorem twoBits_forbidden (T : Task) : forbidden twoBits.statistics T = 0 := by
  unfold forbidden
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  exact twoBits_keeps T i j (T i) (T j) (i, j) (Quantum.Proofs.statistics_forbidden T i j)

theorem twoBits_F4 : F4 twoBits.statistics = 0 := by
  unfold F4
  exact Finset.sum_eq_zero fun T _ => twoBits_forbidden T

/-- With unbiased outcomes, no forbidden mass in a task is CE = 1 in that task. -/
theorem twoBits_CE (T : Task) : CE twoBits.statistics T = 1 := by
  rw [PBRExclusion.Proofs.CE_eq_of_unbiased twoBits bitSame_unbiased bitFlip_unbiased,
    twoBits_forbidden]
  norm_num

theorem twoBits_CE4 : CE4 twoBits.statistics = 1 := by
  rw [Model.CE4_eq twoBits bitSame_unbiased bitFlip_unbiased, twoBits_F4]
  norm_num

/-- In the task `0+` the renaming changes nothing, so the model gives what `twoBitsRaw` gives. -/
theorem twoBits_state00 :
    twoBits.statistics 0 0 ![0, 0] 0 0 (0, 1) = 1 / 4 ∧
      twoBits.statistics 0 0 ![0, 0] 0 0 (1, 0) = 0 := by
  have h (z : Outcome) : relabel ![0, 0] z = z := by simp [relabel]
  have h2 := twoBits_statistics ![0, 0] 0 0 0 0 (0, 1)
  have h3 := twoBits_statistics ![0, 0] 0 0 0 0 (1, 0)
  rw [h] at h2 h3
  obtain ⟨r2, r3⟩ := twoBitsRaw_state00 ![0, 0]
  exact ⟨h2.trans r2, h3.trans r3⟩

/-- The second state of a task, `ρ_{2|T}`, is prepared with probability one quarter, and it always
gets `Y = 3`. -/
theorem twoBits_state2 (T : Task) :
    twoBits.statistics 0 1 T (T 0) (T 1) (1, 0) = 1 / 4 := by
  have key : ∀ a b : Fin 2, ∑ lA : Fin 2, ∑ lB : Fin 2, (1 / 2 : ℝ) * (1 / 2) *
      ((if lA = a then 1 else 0) * (if lB + 1 = b then 1 else 0) *
        (if (if a = b then ((lA + lB, lA + lB + 1) : Outcome)
          else ((lA + lB, lA + lB + 1) : Outcome).swap) = (1, 0) then 1 else 0)) = 1 / 4 := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two] <;> norm_num
  simpa [Model.statistics, twoBits, DetSource.toSource, bitSame, bitFlip, relabel] using
    key (T 0) (T 1)

/-- The third state of a task, `ρ_{3|T}`, always gets `Y = 2`. -/
theorem twoBits_state3 (T : Task) :
    twoBits.statistics 1 0 T (T 1) (T 0) (0, 1) = 1 / 4 := by
  have key : ∀ a b : Fin 2, ∑ lA : Fin 2, ∑ lB : Fin 2, (1 / 2 : ℝ) * (1 / 2) *
      ((if lA = b then 1 else 0) * (if lB = a then 1 else 0) *
        (if (if a = b then ((lA + lB, lA + lB + 1) : Outcome)
          else ((lA + lB, lA + lB + 1) : Outcome).swap) = (0, 1) then 1 else 0)) = 1 / 4 := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two] <;> norm_num
  simpa [Model.statistics, twoBits, DetSource.toSource, bitSame, bitFlip, relabel] using
    key (T 0) (T 1)

/-- Each state of a task is prepared with probability one quarter. -/
theorem twoBits_prepared (T : Task) (sA sB xA xB : Fin 2) :
    ∑ y, twoBits.statistics sA sB T xA xB y = 1 / 4 := by
  rw [Model.sum_statistics, twoBits_unbiased.1 sA xA, twoBits_unbiased.2 sB xB]
  norm_num

/-- The two sources give `|+⟩` different distributions. -/
theorem twoBits_plus :
    twoBits.A.μ 1 0 0 = 1 ∧ twoBits.B.μ 1 0 0 = 0 := by
  constructor
  · change bitSame.toSource.μ 1 0 0 = 1
    rw [bitSame_μ]; simp
  · change bitFlip.toSource.μ 1 0 0 = 0
    rw [bitFlip_μ]; simp

theorem twoBitsAB_μ (s x l : Fin 2) :
    twoBitsAB.μA s x l = twoBits.A.μ s x l ∧ twoBitsAB.μB s x l = twoBits.B.μ s x l := by
  constructor
  · change _ = bitSame.toSource.μ s x l
    rw [bitSame_μ]
    rfl
  · change _ = bitFlip.toSource.μ s x l
    rw [bitFlip_μ]
    rfl

theorem twoBitsAB_identity : twoBitsAB.Identity := by
  constructor <;> intro l <;> fin_cases l <;> simp [twoBitsAB]

theorem twoBitsAB_CE (T : Task) : twoBitsAB.CE T = 1 := by
  have h : twoBitsAB.CE T =
      (PBRExclusion.Proofs.abOfModel twoBits twoBits_unbiased.1 twoBits_unbiased.2).CE T := by
    simp only [OntologicalModelAB.CE, twoBitsAB, PBRExclusion.Proofs.abOfModel]
    simp only [show twoBits.A = bitSame.toSource from rfl,
      show twoBits.B = bitFlip.toSource from rfl,
      bitSame_μ, bitFlip_μ]
  rw [h, PBRExclusion.Proofs.abOfModel_CE, twoBits_CE]

theorem twoBitsAB_CE4 : twoBitsAB.CE4 = 1 := by
  unfold OntologicalModelAB.CE4
  simp only [twoBitsAB_CE]
  rw [PBRExclusion.Proofs.sum_pair_one]
  norm_num

theorem twoBits_ξ_Y1_Y4 (T : Task) (lA lB : Fin 2) :
    twoBits.ξ T lA lB (0, 0) = 0 ∧ twoBits.ξ T lA lB (1, 1) = 0 := by
  rw [twoBits_ξ_eq, twoBits_ξ_eq]
  have key : ∀ c : Fin 2, ((0, 0) : Outcome) ≠ (c, c + 1) ∧ ((1, 1) : Outcome) ≠ (c, c + 1) := by
    decide
  obtain ⟨h1, h4⟩ := key (lA + lB + T 0 + T 1)
  exact ⟨by simp [h1], by simp [h4]⟩


/-! ## The two-bit model among the models with ontic states in any probability space -/

theorem ofFinite_twoBits :
    (General.Model.ofFinite twoBits).A.Unbiased ∧ (General.Model.ofFinite twoBits).B.Unbiased ∧
      (∀ T sA sB xA xB y, Quantum.statistics sA sB T xA xB y = 0 →
        (General.Model.ofFinite twoBits).statistics sA sB T xA xB y = 0) ∧
      F4 (General.Model.ofFinite twoBits).statistics = 0 ∧
      CE4 (General.Model.ofFinite twoBits).statistics = 1 := by
  rw [General.Model.ofFinite_statistics]
  exact ⟨General.Proofs.ofFinite_unbiased _ bitSame_unbiased,
    General.Proofs.ofFinite_unbiased _ bitFlip_unbiased, twoBits_keeps, twoBits_F4, twoBits_CE4⟩


end

end PBRExclusion.Support.Proofs
