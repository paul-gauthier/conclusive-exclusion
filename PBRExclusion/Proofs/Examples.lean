import PBRExclusion.Proofs.Bound

/-!
# Proofs for the explicit models

This file proves the joint overlaps, marginals and distributions of the explicit sources, and the CE
of the two further models. The statements are in `PBRExclusion/Statements.lean`.

A model `avoiding A B` has one response function, built from `avoid`. Every number below about such
a model comes from one fact (`statistics_avoiding`). The measurement excludes a state that was
prepared only when both sources' outcomes are the task's, and it then excludes the state of the
setting `T 0` on each qubit.
-/

namespace PBRExclusion.Proofs

noncomputable section

variable {Λ ΛA ΛB : Type*} [Fintype Λ] [Fintype ΛA] [Fintype ΛB]

/-! ## The rule `avoid` -/

/-- Two pairs are equal when they agree under both settings. -/
theorem pair_ext_iff (f g : Pair) : f = g ↔ f 0 = g 0 ∧ f 1 = g 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1

/-- When the outcomes are the task's, `avoid` gives `T 0`. -/
theorem avoid_self (T : Task) : avoid T T = T 0 := by
  simp [avoid]

/-- `avoid` gives a setting at which the outcome is the task's only when both outcomes are the
task's. -/
theorem avoid_spec (outcomes T : Task) :
    outcomes (avoid outcomes T) = T (avoid outcomes T) ↔ outcomes = T := by
  constructor
  · intro h
    unfold avoid at h
    split_ifs at h with h0 h1
    · exact absurd h h0
    · exact absurd h h1
    · exact (pair_ext_iff _ _).2 ⟨by simpa using h0, by simpa using h1⟩
  · rintro rfl
    rfl

/-- This is one source's part of the response function of `avoiding`. -/
theorem ite_mul_ite_avoid (outcomes T : Task) (i : Fin 2) :
    (if outcomes i = T i then (1 : ℝ) else 0) * (if avoid outcomes T = i then 1 else 0) =
      if outcomes = T ∧ T 0 = i then 1 else 0 := by
  by_cases h : avoid outcomes T = i
  · subst h
    by_cases h' : outcomes = T
    · subst h'
      simp [avoid_self]
    · have h'' : ¬ outcomes (avoid outcomes T) = T (avoid outcomes T) := fun e =>
        h' ((avoid_spec _ _).1 e)
      simp [h', h'']
  · have h' : ¬ (outcomes = T ∧ T 0 = i) := by
      rintro ⟨rfl, h0⟩
      exact h (by rw [avoid_self]; exact h0)
    simp [h, h']

/-! ## Sources with deterministic outcomes -/

theorem jointOverlap_toSource (D : DetSource Λ) (T : Task) :
    D.toSource.jointOverlap T = ∑ l, if D.outcomes l = T then D.p l else 0 := by
  unfold Source.jointOverlap
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [DetSource.toSource]
  by_cases h0 : D.outcomes l 0 = T 0 <;> by_cases h1 : D.outcomes l 1 = T 1 <;>
    simp [pair_ext_iff, h0, h1]

/-- The mass on which one source has the task's outcomes and `avoid` gives the setting `i`. -/
theorem sum_mul_ite_avoid (D : DetSource Λ) (T : Task) (i : Fin 2) :
    ∑ l, D.p l * ((if D.outcomes l i = T i then (1 : ℝ) else 0) *
        (if avoid (D.outcomes l) T = i then 1 else 0)) =
      if T 0 = i then D.toSource.jointOverlap T else 0 := by
  simp_rw [ite_mul_ite_avoid]
  rw [jointOverlap_toSource]
  by_cases h : T 0 = i <;> simp [h]

/-! ## The models `avoiding A B` -/

/-- The measurement of `avoiding` obeys one rule. The probability that a task's state `(i, j)` is
prepared and excluded is zero unless `(i, j)` is `(T 0, T 0)`, and then it is the product of the two
joint overlaps. -/
theorem statistics_avoiding (A : DetSource ΛA) (B : DetSource ΛB) (T : Task) (i j : Fin 2) :
    (avoiding A B).statistics i j T (T i) (T j) (i, j) =
      (if T 0 = i then A.toSource.jointOverlap T else 0) *
        (if T 0 = j then B.toSource.jointOverlap T else 0) := by
  have hy : ∀ u v : Fin 2, (if (u, v) = (i, j) then (1 : ℝ) else 0) =
      (if u = i then 1 else 0) * (if v = j then 1 else 0) := by
    intro u v
    by_cases hu : u = i <;> by_cases hv : v = j <;> simp [hu, hv]
  rw [← sum_mul_ite_avoid A T i, ← sum_mul_ite_avoid B T j, Finset.sum_mul_sum]
  simp only [Model.statistics, avoiding, DetSource.toSource, hy]
  refine Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
  ring

/-- A task's forbidden mass is the product of the two joint overlaps, so
`jointOverlap_mul_le_forbidden` holds with equality. -/
theorem forbidden_avoiding_eq (A : DetSource ΛA) (B : DetSource ΛB) (T : Task) :
    forbidden (avoiding A B).statistics T =
      A.toSource.jointOverlap T * B.toSource.jointOverlap T := by
  unfold forbidden
  simp_rw [statistics_avoiding]
  rw [← Finset.sum_mul_sum]
  simp

theorem forbidden_avoiding (A : DetSource ΛA) (B : DetSource ΛB) (T : Task) :
    forbidden (avoiding A B).statistics T =
      (∑ lA, if A.outcomes lA = T then A.p lA else 0) *
        ∑ lB, if B.outcomes lB = T then B.p lB else 0 := by
  rw [forbidden_avoiding_eq, jointOverlap_toSource, jointOverlap_toSource]

theorem F4_avoiding (A : DetSource ΛA) (B : DetSource ΛB) :
    F4 (avoiding A B).statistics =
      ∑ T : Task, A.toSource.jointOverlap T * B.toSource.jointOverlap T := by
  unfold F4
  simp_rw [forbidden_avoiding_eq]

/-! ## The four sources -/

theorem bitSame_jointOverlap (T : Task) :
    bitSame.toSource.jointOverlap T = if T 0 = T 1 then 1 / 2 else 0 := by
  rw [jointOverlap_toSource]
  simp only [bitSame, pair_ext_iff, Fin.sum_univ_two]
  generalize T 0 = a
  generalize T 1 = b
  fin_cases a <;> fin_cases b <;> simp

theorem bitFlip_jointOverlap (T : Task) :
    bitFlip.toSource.jointOverlap T = if T 0 = T 1 then 0 else 1 / 2 := by
  rw [jointOverlap_toSource]
  simp only [bitFlip, pair_ext_iff, Fin.sum_univ_two]
  generalize T 0 = a
  generalize T 1 = b
  fin_cases a <;> fin_cases b <;> simp

theorem toyBit_jointOverlap (T : Task) : toyBit.toSource.jointOverlap T = 1 / 4 := by
  rw [jointOverlap_toSource]
  simp [toyBit]

theorem bitSame_unbiased : bitSame.toSource.Unbiased := by
  intro s x
  simp only [Source.marginal, DetSource.toSource, bitSame, Fin.sum_univ_two]
  fin_cases x <;> simp

theorem bitFlip_unbiased : bitFlip.toSource.Unbiased := by
  intro s x
  simp only [Source.marginal, DetSource.toSource, bitFlip, Fin.sum_univ_two]
  fin_cases s <;> fin_cases x <;> simp

theorem bitSame_β (T : Task) : bitSame.toSource.β T = if T 0 = T 1 then 1 else 0 := by
  rw [β_eq_two_mul_jointOverlap _ bitSame_unbiased, bitSame_jointOverlap]
  split_ifs <;> norm_num

theorem bitFlip_β (T : Task) : bitFlip.toSource.β T = if T 0 = T 1 then 0 else 1 := by
  rw [β_eq_two_mul_jointOverlap _ bitFlip_unbiased, bitFlip_jointOverlap]
  split_ifs <;> norm_num

theorem toyBit_unbiased : toyBit.toSource.Unbiased := by
  intro s x
  simp only [Source.marginal, DetSource.toSource, toyBit, sum_pair]
  fin_cases s <;> fin_cases x <;> simp <;> norm_num

/-- The biased source's marginals, in a form that `simp` can use. -/
theorem biasedTrit_marginal_eq (s x : Fin 2) :
    biasedTrit.toSource.marginal s x = if x = 0 then 3 / 4 else 1 / 4 := by
  simp only [Source.marginal, DetSource.toSource, biasedTrit, Fin.sum_univ_three]
  fin_cases s <;> fin_cases x <;> simp <;> norm_num

theorem biasedTrit_marginal (s : Fin 2) :
    biasedTrit.toSource.marginal s 0 = 3 / 4 ∧ biasedTrit.toSource.marginal s 1 = 1 / 4 := by
  simp [biasedTrit_marginal_eq]

theorem bitSame_μ (s x l : Fin 2) :
    bitSame.toSource.μ s x l = if l = x then 1 else 0 := by
  simp only [Source.μ, bitSame_unbiased s x]
  simp only [DetSource.toSource, bitSame]
  by_cases h : l = x <;> simp [h]

theorem bitFlip_μ (s x l : Fin 2) :
    bitFlip.toSource.μ s x l = if l + s = x then 1 else 0 := by
  simp only [Source.μ, bitFlip_unbiased s x]
  simp only [DetSource.toSource, bitFlip]
  by_cases h : l + s = x <;> simp [h]

theorem biasedTrit_μ_ne :
    1 / 2 * biasedTrit.toSource.μ 0 0 1 + 1 / 2 * biasedTrit.toSource.μ 0 1 1 ≠
      1 / 2 * biasedTrit.toSource.μ 1 0 1 + 1 / 2 * biasedTrit.toSource.μ 1 1 1 :=
      by
  simp only [Source.μ, biasedTrit_marginal_eq]
  simp only [DetSource.toSource, biasedTrit]
  norm_num

/-! ## Source A of the two-bit model for both qubits -/

theorem twoBitsAlike_F4 : F4 twoBitsAlike.statistics = 1 / 2 := by
  unfold twoBitsAlike
  rw [F4_avoiding, sum_pair]
  simp only [bitSame_jointOverlap]
  norm_num

theorem twoBitsAlike_CE4 : CE4 twoBitsAlike.statistics = 7 / 8 := by
  rw [CE4_eq twoBitsAlike bitSame_unbiased bitSame_unbiased, twoBitsAlike_F4]
  norm_num

/-! ## The toy bit on both qubits -/

theorem toy_F4 : F4 toy.statistics = 1 / 4 := by
  unfold toy
  rw [F4_avoiding, sum_pair]
  simp only [toyBit_jointOverlap]
  norm_num

theorem toy_CE4 : CE4 toy.statistics = 15 / 16 := by
  rw [CE4_eq toy toyBit_unbiased toyBit_unbiased, toy_F4]
  norm_num

/-! ## Tightness -/

theorem exists_same_source_CE4_eq :
    ∃ M : Model Pair Pair, M.A = M.B ∧ M.A.Unbiased ∧ F4 M.statistics = 1 / 4 ∧
      CE4 M.statistics = 15 / 16 :=
  ⟨toy, rfl, toyBit_unbiased, toy_F4, toy_CE4⟩

end

end PBRExclusion.Proofs
