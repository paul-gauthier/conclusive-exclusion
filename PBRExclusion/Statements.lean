import PBRExclusion.Proofs.AppendixB

/-!
# Statements for finite ontic state spaces

Each statement in this file is proved. What follows its `:=` is the name of the proof in
`PBRExclusion/Proofs/`, so the file can be read without the proofs.

The definitions are in `PBRExclusion/Defs.lean`. The paper is Yīng, Schmid and Spekkens,
arXiv:2512.04173v5, and equation numbers are those of its PDF.
`PBRExclusion/GeneralStatements.lean` has the bounds for classical causal models again, with
ontic states in any probability space.
-/

namespace PBRExclusion

noncomputable section

variable {Λ ΛA ΛB : Type*} [Fintype Λ] [Fintype ΛA] [Fintype ΛB]

/-! ## Appendix B -/

/-- This is the paper's (B40). Given the ontological identity (B4), the four `β_T` sum to at
least 2. -/
theorem OntologicalModel.two_le_sum_β (N : OntologicalModel Λ) (h : N.Identity) :
    2 ≤ ∑ T : Task, N.β T := Proofs.two_le_sum_β N h

/-- This is the paper's (B8), which is written there for the task `0+`, with (B9) to (B12) for
the four tasks. In the task `T`, `CE_T` is at most `1 - β_T ^ 2 / 4`, and the square is there
because both qubits have the same four distributions. -/
theorem OntologicalModel.CE_le (N : OntologicalModel Λ) (T : Task) :
    N.CE T ≤ 1 - 1 / 4 * N.β T ^ 2 := Proofs.ontological_CE_le N T

/-- This is the paper's inequality (12). Given the ontological identity (B4), CE is at most
15/16. -/
theorem OntologicalModel.CE4_le (N : OntologicalModel Λ) (h : N.Identity) : N.CE4 ≤ 15 / 16 :=
  Proofs.ontological_CE4_le N h

/-- Spekkens' toy bit satisfies the ontological identity. -/
theorem toyOntological_identity : toyOntological.Identity := Proofs.toyOntological_identity

/-- The CE of Spekkens' toy bit is 15/16. -/
theorem toyOntological_CE4 : toyOntological.CE4 = 15 / 16 := Proofs.toyOntological_CE4

/-- The bound of inequality (12) is tight, as the paper shows in (B42). Some ontological model
satisfies (B4) and has CE exactly 15/16. -/
theorem exists_ontologicalModel_CE4_eq :
    ∃ N : OntologicalModel Pair, N.Identity ∧ N.CE4 = 15 / 16 :=
  Proofs.exists_ontologicalModel_CE4_eq

/-! ## Appendix B with distributions for each qubit -/

/-- With distributions for each qubit, the step of (B8) gives the product of the two qubits'
`β_T`, where the paper has the square of one. -/
theorem OntologicalModelAB.CE_le (N : OntologicalModelAB ΛA ΛB) (T : Task) :
    N.CE T ≤ 1 - 1 / 4 * (N.βA T * N.βB T) := Proofs.ab_CE_le N T

/-- If each qubit satisfies the ontological identity, and the two qubits have the same `β_T` in
every task, then CE is at most 15/16. -/
theorem OntologicalModelAB.CE4_le (N : OntologicalModelAB ΛA ΛB) (h : N.Identity)
    (hβ : ∀ T, N.βA T = N.βB T) : N.CE4 ≤ 15 / 16 := Proofs.ab_CE4_le N h hβ

/-- An ontological model of Appendix B, as a model with distributions for each qubit, has the
same `CE_T` in each task. -/
theorem OntologicalModel.toAB_CE (N : OntologicalModel Λ) (T : Task) : N.toAB.CE T = N.CE T :=
  Proofs.toAB_CE N T

/-- `N.toAB` satisfies the ontological identity on each qubit when `N` satisfies (B4). -/
theorem OntologicalModel.toAB_identity (N : OntologicalModel Λ) (h : N.Identity) :
    N.toAB.Identity := Proofs.toAB_identity N h

/-- The two qubits of `N.toAB` have the same `β_T`, which is the `β_T` of `N`. So Appendix B is
the case of `OntologicalModelAB.CE4_le` in which the two qubits have the same distributions. -/
theorem OntologicalModel.toAB_β (N : OntologicalModel Λ) (T : Task) :
    N.toAB.βA T = N.β T ∧ N.toAB.βB T = N.β T := Proofs.toAB_β N T

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

/-- With unbiased outcomes, the paper's `CE_T` is one minus the forbidden mass of the task. -/
theorem Model.CE_eq (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    CE M.statistics T = 1 - forbidden M.statistics T := Proofs.CE_eq_of_unbiased M hA hB T

/-- With unbiased outcomes, the paper's CE is `1 - F4 / 4`. -/
theorem Model.CE4_eq (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    CE4 M.statistics = 1 - F4 M.statistics / 4 := Proofs.CE4_eq M hA hB

/-! ## The ontological identity on a source -/

/-- On a source with unbiased outcomes, the four distributions `μ` satisfy the ontological
identity (B4). Appendix C states this constraint for any classical causal model with the causal
structure of the bilocality scenario, and it holds for each source separately. -/
theorem Source.ontological_identity (S : Source Λ) (h : S.Unbiased) (l : Λ) :
    1 / 2 * S.μ 0 0 l + 1 / 2 * S.μ 0 1 l = 1 / 2 * S.μ 1 0 l + 1 / 2 * S.μ 1 1 l :=
  Proofs.μ_identity S h l

/-- The source `biasedTrit` reports 1 with probability 1/4 under each setting. -/
theorem biasedTrit_marginal (s : Fin 2) :
    biasedTrit.toSource.marginal s 0 = 3 / 4 ∧ biasedTrit.toSource.marginal s 1 = 1 / 4 :=
  Proofs.biasedTrit_marginal s

/-- The ontological identity with weights of one half needs unbiased outcomes. On the source
`biasedTrit` its two sides differ at the ontic state 1. -/
theorem biasedTrit_μ_ne :
    1 / 2 * biasedTrit.toSource.μ 0 0 1 + 1 / 2 * biasedTrit.toSource.μ 0 1 1 ≠
      1 / 2 * biasedTrit.toSource.μ 1 0 1 + 1 / 2 * biasedTrit.toSource.μ 1 1 1 :=
  Proofs.biasedTrit_μ_ne

/-- A classical causal model with unbiased outcomes is an ontological model with distributions
for each qubit. The distributions are the two sources' `μ`, they satisfy the ontological identity
on each qubit, the response function is the model's, and each task has the same `CE_T`. -/
theorem Model.exists_ontologicalModelAB (M : Model ΛA ΛB) (hA : M.A.Unbiased)
    (hB : M.B.Unbiased) :
    ∃ N : OntologicalModelAB ΛA ΛB, N.Identity ∧ (∀ s x l, N.μA s x l = M.A.μ s x l) ∧
      (∀ s x l, N.μB s x l = M.B.μ s x l) ∧ (∀ T lA lB y, N.ξ T lA lB y = M.ξ T lA lB y) ∧
      ∀ T, N.CE T = CE M.statistics T := Proofs.exists_ontologicalModelAB M hA hB

/-- A classical causal model whose two sources are independent copies of one unbiased source is
an ontological model of Appendix B. Its four distributions satisfy (B4), and each task has the
same `CE_T`. -/
theorem Model.exists_ontologicalModel (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    ∃ N : OntologicalModel Λ, N.Identity ∧ (∀ s x l, N.μ s x l = M.A.μ s x l) ∧
      ∀ T, N.CE T = CE M.statistics T := Proofs.exists_ontologicalModel M h hU

/-- Every ontological model of Appendix B that satisfies (B4) arises in that way, from a
classical causal model with two independent copies of one unbiased source. -/
theorem OntologicalModel.exists_model (N : OntologicalModel Λ) (h : N.Identity) :
    ∃ M : Model Λ Λ, M.A = M.B ∧ M.A.Unbiased ∧ (∀ s x l, M.A.μ s x l = N.μ s x l) ∧
      ∀ T, PBRExclusion.CE M.statistics T = N.CE T := Proofs.ontological_exists_model N h

/-! ## The steps of Appendix B for two sources -/

/-- This pointwise identity is behind (B40). The paper states it where all four distributions are
positive, in the unnumbered equation after (B37), and the same identity holds for all reals. -/
theorem sum_min_eq_add_two_mul_min {a₀ a₁ b₀ b₁ : ℝ} (h : a₀ + a₁ = b₀ + b₁) :
    min a₀ b₀ + min a₀ b₁ + min a₁ b₀ + min a₁ b₁ = a₀ + a₁ + 2 * min (min a₀ a₁) (min b₀ b₁) :=
  Proofs.sum_min_eq_add_two_mul_min h

/-- On any source the four joint overlaps sum to at least one. With unbiased outcomes this is
(B40), since a joint overlap is then half of `β_T`. -/
theorem Source.one_le_sum_jointOverlap (S : Source Λ) : 1 ≤ ∑ T : Task, S.jointOverlap T :=
  Proofs.one_le_sum_jointOverlap S

/-- In any classical causal model and any task, the forbidden mass is at least the product of the
two sources' joint overlaps. This is the step of (B8), with a factor for each source. -/
theorem Model.jointOverlap_mul_le_forbidden (M : Model ΛA ΛB) (T : Task) :
    M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T :=
  Proofs.jointOverlap_mul_le_forbidden M T

/-- On a source with unbiased outcomes, the paper's `β_T` is twice the joint overlap. -/
theorem Source.β_eq (S : Source Λ) (h : S.Unbiased) (T : Task) : S.β T = 2 * S.jointOverlap T :=
  Proofs.β_eq_two_mul_jointOverlap S h T

/-- With unbiased outcomes, `CE_T` is at most one minus a quarter of the product of the two
sources' `β_T`. This is the step of (B8) in the paper's form, with a `β_T` for each source. -/
theorem Model.CE_le (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    CE M.statistics T ≤ 1 - 1 / 4 * (M.A.β T * M.B.β T) := Proofs.CE_le_β M hA hB T

/-- If the two sources have equal joint overlaps, the four tasks have forbidden mass at least one
quarter. The two sources may have different ontic state spaces. -/
theorem Model.quarter_le_F4_of_jointOverlap_eq (M : Model ΛA ΛB)
    (h : ∀ T, M.A.jointOverlap T = M.B.jointOverlap T) : 1 / 4 ≤ F4 M.statistics :=
  Proofs.quarter_le_F4_of_jointOverlap_eq M h

/-- When the two sources are independent copies of one source, the four tasks have forbidden mass
at least one quarter. -/
theorem Model.quarter_le_F4 (M : Model Λ Λ) (h : M.A = M.B) : 1 / 4 ≤ F4 M.statistics :=
  Proofs.quarter_le_F4 M h

/-- When the two sources are independent copies of one source with unbiased outcomes, CE is at
most 15/16, whatever the joint measurement. -/
theorem Model.CE4_le (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    CE4 M.statistics ≤ 15 / 16 := Proofs.CE4_le M h hU

/-! ## The two sources of the two-bit model -/

/-- Source A of the two-bit model has unbiased outcomes. -/
theorem bitSame_unbiased : bitSame.toSource.Unbiased := Proofs.bitSame_unbiased

/-- Source B of the two-bit model has unbiased outcomes. -/
theorem bitFlip_unbiased : bitFlip.toSource.Unbiased := Proofs.bitFlip_unbiased

/-- At source A the ontic bit is the outcome under either setting. So `|0⟩` and `|+⟩` have the
same distribution, and so do `|1⟩` and `|-⟩`. -/
theorem bitSame_μ (s x l : Fin 2) :
    bitSame.toSource.μ s x l = if l = x then 1 else 0 := Proofs.bitSame_μ s x l

/-- At source B the ontic bit is the outcome under `Z` and the opposite of the outcome under `X`.
So `|0⟩` and `|-⟩` have the same distribution, and so do `|1⟩` and `|+⟩`. -/
theorem bitFlip_μ (s x l : Fin 2) :
    bitFlip.toSource.μ s x l = if l + s = x then 1 else 0 := Proofs.bitFlip_μ s x l

/-- With deterministic outcomes, the joint overlap on a task is the probability that the outcomes
are the task's. -/
theorem DetSource.jointOverlap_toSource (D : DetSource Λ) (T : Task) :
    D.toSource.jointOverlap T = ∑ l, if D.outcomes l = T then D.p l else 0 :=
  Proofs.jointOverlap_toSource D T

/-- The joint overlap of source A is one half on the tasks `0+` and `1-`, and zero on `0-` and
`1+`. -/
theorem bitSame_jointOverlap (T : Task) :
    bitSame.toSource.jointOverlap T = if T 0 = T 1 then 1 / 2 else 0 :=
  Proofs.bitSame_jointOverlap T

/-- The joint overlap of source B is zero on the tasks `0+` and `1-`, and one half on `0-` and
`1+`. -/
theorem bitFlip_jointOverlap (T : Task) :
    bitFlip.toSource.jointOverlap T = if T 0 = T 1 then 0 else 1 / 2 :=
  Proofs.bitFlip_jointOverlap T

/-- The paper's `β_T` for source A is 1 on the tasks `0+` and `1-`, and 0 on `0-` and `1+`. -/
theorem bitSame_β (T : Task) : bitSame.toSource.β T = if T 0 = T 1 then 1 else 0 :=
  Proofs.bitSame_β T

/-- The paper's `β_T` for source B is 0 on the tasks `0+` and `1-`, and 1 on `0-` and `1+`. So in
every task one of the two sources has `β_T = 0`. -/
theorem bitFlip_β (T : Task) : bitFlip.toSource.β T = if T 0 = T 1 then 0 else 1 :=
  Proofs.bitFlip_β T

/-! ## Two more models -/

/-- With deterministic outcomes and the measurement of `avoiding`, a task's forbidden mass is the
probability that both sources' outcomes are the task's. -/
theorem forbidden_avoiding (A : DetSource ΛA) (B : DetSource ΛB) (T : Task) :
    forbidden (avoiding A B).statistics T =
      (∑ lA, if A.outcomes lA = T then A.p lA else 0) *
        ∑ lB, if B.outcomes lB = T then B.p lB else 0 :=
  Proofs.forbidden_avoiding A B T

/-- With source A of the two-bit model for both qubits, the forbidden mass of the four tasks is
one half. -/
theorem twoBitsAlike_F4 : F4 twoBitsAlike.statistics = 1 / 2 := Proofs.twoBitsAlike_F4

/-- With source A of the two-bit model for both qubits, CE is 7/8. -/
theorem twoBitsAlike_CE4 : CE4 twoBitsAlike.statistics = 7 / 8 := Proofs.twoBitsAlike_CE4

/-- Spekkens' toy bit has unbiased outcomes. -/
theorem toyBit_unbiased : toyBit.toSource.Unbiased := Proofs.toyBit_unbiased

/-- With the toy bit for both qubits, the forbidden mass of the four tasks is one quarter. -/
theorem toy_F4 : F4 toy.statistics = 1 / 4 := Proofs.toy_F4

/-- With the toy bit for both qubits, CE is 15/16. -/
theorem toy_CE4 : CE4 toy.statistics = 15 / 16 := Proofs.toy_CE4

/-- The bound for two independent copies of one unbiased source is tight. The toy bit for both
qubits has unbiased outcomes, forbidden mass 1/4 and CE = 15/16. -/
theorem exists_same_source_CE4_eq :
    ∃ M : Model Pair Pair, M.A = M.B ∧ M.A.Unbiased ∧ F4 M.statistics = 1 / 4 ∧
      CE4 M.statistics = 15 / 16 := Proofs.exists_same_source_CE4_eq

end

end PBRExclusion
