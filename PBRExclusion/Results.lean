import PBRExclusion.SupportStatements

/-!
# The main results

This file restates the main results in one place. Each theorem here is proved in a few lines
from a statement of the library, so the file can be read with the four definitions files and
without the others. The paper is Yīng, Schmid and Spekkens, arXiv:2512.04173v5, and equation
numbers are those of its PDF.

1. The paper's inequality (12) holds for the ontological model of Appendix B, with a finite ontic
   state space.
2. In the bilocality scenario a classical causal model with two ontic bits has CE = 1.
3. The ontological identity holds at each source of that model. Its two sources represent the
   states differently, and the step of (B8) then gives a product of two `β_T`, one of which is
   zero in each task.
4. The same holds in the form of Appendix B, for an ontological model with distributions for
   each qubit.
5. The bilocality scenario has a possibilistic gap. No classical causal model within it has
   exactly the support of the quantum statistics.
6. Quantum theory reaches CE = 1, and two Bell pairs with steering give the quantum statistics.

## Where the definitions are

* `PBRExclusion/Defs.lean` has tasks, statistics, `CE`, classical causal models with finite ontic
  state spaces (`Model`), the ontological model of Appendix B (`OntologicalModel`) and the
  two-bit model (`twoBits`).
* `PBRExclusion/GeneralDefs.lean` has classical causal models with ontic states in any
  probability space (`General.Model`).
* `PBRExclusion/QuantumDefs.lean` has the quantum experiment (`Quantum.statistics`), and
  `PBRExclusion/NetworkDefs.lean` has it with two Bell pairs and steering (`Quantum.bellModel`).

## Conventions

* A setting is `0` for `Z` and `1` for `X`. A label `(s, x)` names a state, and it is `|0⟩`,
  `|1⟩`, `|+⟩`, `|-⟩` for `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`.
* A task `T` is the paper's `0+`, `0-`, `1+`, `1-` for `![0,0]`, `![0,1]`, `![1,0]`, `![1,1]`.
  The outcomes `Y1` to `Y4` are the paper's `Y = 1` to `Y = 4`.
* Settings, outcomes and bits are in `Fin 2`, where `+` is addition modulo 2.
* A classical causal model is always one within the bilocality scenario. Its two sources are
  classical models of the paper's multi-sources.
* A source has unbiased outcomes when each outcome has probability one half under each setting.
* The forbidden mass of a task adds up, over the task's four states, the probability that the
  state is prepared and the outcome excludes it.
* The joint overlap of a source on a task is half of the paper's `β_T` when the outcomes are
  unbiased, and it is defined without that assumption.
* An event is a setting for each source, a task and the three outcomes. An impossible event of
  some statistics is an event of probability zero, and the support is the set of the other
  events.
-/

namespace PBRExclusion.Results

open MeasureTheory

noncomputable section

/-! ## 1. The paper's inequality (12) -/

/-- Inequality (12) holds for the ontological model of Appendix B, in which both qubits have the
same four distributions `μ`. If these satisfy the ontological identity (B4), CE is at most 15/16.
The identity is a hypothesis here, and noncontextuality is not formalized. The ontic state space
is finite in this form, and `bound_for_one_source` below has the same bound for any probability
space. -/
theorem inequality_12 {Λ : Type*} [Fintype Λ] (N : OntologicalModel Λ) (h : N.Identity) :
    N.CE4 ≤ 15 / 16 := OntologicalModel.CE4_le N h

/-- The bound of inequality (12) is tight, as the paper shows in (B42). -/
theorem inequality_12_tight : ∃ N : OntologicalModel Pair, N.Identity ∧ N.CE4 = 15 / 16 :=
  exists_ontologicalModel_CE4_eq

/-- The paper's (B8) bounds `CE_T` by the square of `β_T`. The paper writes it for the task
`0+`. -/
theorem eq_B8 {Λ : Type*} [Fintype Λ] (N : OntologicalModel Λ) (T : Task) :
    N.CE T ≤ 1 - 1 / 4 * N.β T ^ 2 := OntologicalModel.CE_le N T

/-- The paper's (B40) is the step that uses the ontological identity. -/
theorem eq_B40 {Λ : Type*} [Fintype Λ] (N : OntologicalModel Λ) (h : N.Identity) :
    2 ≤ ∑ T : Task, N.β T := OntologicalModel.two_le_sum_β N h

/-! ## 2. A classical causal model with CE = 1 in the bilocality scenario -/

/-- Each source of the two-bit model emits a uniform bit. Source A reports `X_A = λ_A`, and
source B reports `X_B = λ_B + S_B`. -/
theorem sources (l s x : Fin 2) :
    twoBits.A.p l = 1 / 2 ∧ twoBits.B.p l = 1 / 2 ∧
      twoBits.A.resp s l x = (if l = x then 1 else 0) ∧
      twoBits.B.resp s l x = (if l + s = x then 1 else 0) := ⟨rfl, rfl, rfl, rfl⟩

/-- The joint measurement of the two-bit model gives `Y2` in the task `T` when
`λ_A + λ_B + T 0 + T 1 = 0`, and `Y3` otherwise. -/
theorem joint_measurement (T : Task) (lA lB : Fin 2) (y : Outcome) :
    twoBits.ξ T lA lB y = if y = (lA + lB + T 0 + T 1, lA + lB + T 0 + T 1 + 1) then 1 else 0 :=
  Support.twoBits_ξ_eq T lA lB y

/-- In the two-bit model `Y` is never 1 or 4. -/
theorem never_Y1_or_Y4 (T : Task) (lA lB : Fin 2) :
    twoBits.ξ T lA lB Y1 = 0 ∧ twoBits.ξ T lA lB Y4 = 0 := Support.twoBits_ξ_Y1_Y4 T lA lB

/-- Both sources of the two-bit model have unbiased outcomes, as the quantum experiment has. -/
theorem unbiased : twoBits.A.Unbiased ∧ twoBits.B.Unbiased := Support.twoBits_unbiased

/-- In the two-bit model each product state is prepared with probability one quarter, so the
conditional probabilities in the paper's CE are defined. -/
theorem prepared (T : Task) (sA sB xA xB : Fin 2) :
    ∑ y, twoBits.statistics sA sB T xA xB y = 1 / 4 := Support.twoBits_prepared T sA sB xA xB

/-- In the two-bit model the state `ρ_{2|T}` gives `Y = 3`. It has the settings `(0, 1)` and the
outcomes `(T 0, T 1)`, and all of its probability goes to `Y3`. -/
theorem state_2 (T : Task) : twoBits.statistics 0 1 T (T 0) (T 1) Y3 = 1 / 4 :=
  Support.twoBits_state2 T

/-- In the two-bit model the state `ρ_{3|T}` gives `Y = 2`. It has the settings `(1, 0)` and the
outcomes `(T 1, T 0)`, and all of its probability goes to `Y2`. -/
theorem state_3 (T : Task) : twoBits.statistics 1 0 T (T 1) (T 0) Y2 = 1 / 4 :=
  Support.twoBits_state3 T

/-- In the two-bit model the outcome is never the index of the prepared state, so the forbidden
mass of each task is zero. -/
theorem never_excludes_the_prepared_state (T : Task) : forbidden twoBits.statistics T = 0 :=
  Support.twoBits_forbidden T

/-- The conclusiveness of exclusion of Eq. (7) is 1 in each task for the two-bit model. -/
theorem CE_eq_one (T : Task) : CE twoBits.statistics T = 1 := Support.twoBits_CE T

/-- The paper's CE of Eq. (8) is 1 for the two-bit model. -/
theorem CE4_eq_one : CE4 twoBits.statistics = 1 := Support.twoBits_CE4

/-! ## 3. What the causal structure requires, and what Appendices A and B use -/

/-- The ontological identity holds at source A of the two-bit model. The distributions are those
of the ontic bit given the label, the paper's `μ_0`, `μ_1`, `μ_+` and `μ_-`. The identity holds
at any source with unbiased outcomes (`Source.ontological_identity`), and it is the constraint
that Appendix C states for a classical causal model with this causal structure. -/
theorem identity_A (l : Fin 2) :
    1 / 2 * twoBits.A.μ 0 0 l + 1 / 2 * twoBits.A.μ 0 1 l =
      1 / 2 * twoBits.A.μ 1 0 l + 1 / 2 * twoBits.A.μ 1 1 l :=
  Source.ontological_identity _ Support.twoBits_unbiased.1 l

/-- The ontological identity holds at source B of the two-bit model. -/
theorem identity_B (l : Fin 2) :
    1 / 2 * twoBits.B.μ 0 0 l + 1 / 2 * twoBits.B.μ 0 1 l =
      1 / 2 * twoBits.B.μ 1 0 l + 1 / 2 * twoBits.B.μ 1 1 l :=
  Source.ontological_identity _ Support.twoBits_unbiased.2 l

/-- Source A of the two-bit model gives `|0⟩` and `|+⟩` the same distribution, and likewise `|1⟩`
and `|-⟩`. So at this source `Λ_0 = Λ_+`. Appendix A cites `Λ_0 ≠ Λ_+` for a noncontextual model,
and the causal structure of the bilocality scenario does not require it. -/
theorem same_distribution_A (x l : Fin 2) : twoBits.A.μ 0 x l = twoBits.A.μ 1 x l := by
  change bitSame.toSource.μ 0 x l = bitSame.toSource.μ 1 x l
  rw [bitSame_μ, bitSame_μ]

/-- Source B of the two-bit model gives `|0⟩` and `|-⟩` the same distribution, and likewise `|1⟩`
and `|+⟩`. -/
theorem same_distribution_B (x l : Fin 2) : twoBits.B.μ 0 x l = twoBits.B.μ 1 (x + 1) l := by
  change bitFlip.toSource.μ 0 x l = bitFlip.toSource.μ 1 (x + 1) l
  rw [bitFlip_μ, bitFlip_μ]
  have key : ∀ x l : Fin 2, l + 0 = x ↔ l + 1 = x + 1 := by decide
  simp only [key x l]

/-- The two sources of the two-bit model do not have the same distributions `μ`. The distribution
of `|+⟩` is all on bit 0 at source A and all on bit 1 at source B. -/
theorem different_distributions : twoBits.A.μ 1 0 0 = 1 ∧ twoBits.B.μ 1 0 0 = 0 :=
  Support.twoBits_μ_plus

/-- With a `μ` for each source, the step of (B8) gives the product of the two sources' `β_T`.
This holds for any classical causal model with unbiased outcomes and finite ontic state
spaces. -/
theorem product_of_β {ΛA ΛB : Type*} [Fintype ΛA] [Fintype ΛB] (M : Model ΛA ΛB)
    (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    CE M.statistics T ≤ 1 - 1 / 4 * (M.A.β T * M.B.β T) := Model.CE_le M hA hB T

/-- In the two-bit model one of the two `β_T` is zero in each task. -/
theorem one_β_zero (T : Task) : twoBits.A.β T * twoBits.B.β T = 0 := by
  change bitSame.toSource.β T * bitFlip.toSource.β T = 0
  rw [bitSame_β, bitFlip_β]
  split_ifs <;> simp

/-- The step of (B8) also holds for ontic states in any probability spaces, with no assumption on
the outcomes. The forbidden mass of a task is at least the product of the two sources' joint
overlaps, and with unbiased outcomes a joint overlap is half of `β_T`. -/
theorem product_of_joint_overlaps {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB]
    (M : General.Model ΛA ΛB) (T : Task) :
    M.A.jointOverlap T * M.B.jointOverlap T ≤ forbidden M.statistics T :=
  General.Model.jointOverlap_mul_le_forbidden M T

/-- When the two sources are independent copies of one source, that product is the square of one
joint overlap, as (B8) has the square of one `β_T`. -/
theorem square_of_one_joint_overlap {Λ : Type*} [MeasurableSpace Λ] (M : General.Model Λ Λ)
    (h : M.A = M.B) (T : Task) : M.A.jointOverlap T ^ 2 ≤ forbidden M.statistics T := by
  have key := General.Model.jointOverlap_mul_le_forbidden M T
  rw [← h] at key
  rwa [sq]

/-- When the two sources are independent copies of one source with unbiased outcomes, the bound
holds in the bilocality scenario. CE is at most 15/16, whatever the joint measurement and
whatever probability space the ontic state lives in. -/
theorem bound_for_one_source {Λ : Type*} [MeasurableSpace Λ] (M : General.Model Λ Λ)
    (h : M.A = M.B) (hU : M.A.Unbiased) : CE4 M.statistics ≤ 15 / 16 :=
  General.Model.CE4_le M h hU

/-! ## 4. The same in the form of Appendix B

In the paper's prepare-measure scenario both qubits are prepared in the same states, and Appendix
B gives a state the same distribution on each, with `Λ_A × Λ_B = Λ × Λ`. Inequality (12) is
proved above in that form. In the bilocality scenario of Appendix C a classical causal model has
a source for each qubit, and these statements are for that case. They are about an ontological
model with distributions for each qubit (`OntologicalModelAB`). -/

/-- With distributions for each qubit, (B8) has the product of the two qubits' `β_T`. -/
theorem eq_B8_for_two_qubits {ΛA ΛB : Type*} [Fintype ΛA] [Fintype ΛB]
    (N : OntologicalModelAB ΛA ΛB) (T : Task) : N.CE T ≤ 1 - 1 / 4 * (N.βA T * N.βB T) :=
  OntologicalModelAB.CE_le N T

/-- If each qubit satisfies the ontological identity and the two qubits have the same `β_T` in
every task, inequality (12) holds. An ontological model of Appendix B is such a model
(`OntologicalModel.toAB_β`). -/
theorem inequality_12_for_equal_β {ΛA ΛB : Type*} [Fintype ΛA] [Fintype ΛB]
    (N : OntologicalModelAB ΛA ΛB) (h : N.Identity) (hβ : ∀ T, N.βA T = N.βB T) :
    N.CE4 ≤ 15 / 16 := OntologicalModelAB.CE4_le N h hβ

/-- The two-bit model in this form has the distributions of its two sources
(`Support.twoBitsAB_μ`). Each qubit satisfies the ontological identity (B4), and `CE_T` is 1 in
each task. -/
theorem two_bits_in_this_form : twoBitsAB.Identity ∧ ∀ T, twoBitsAB.CE T = 1 :=
  ⟨Support.twoBitsAB_identity, Support.twoBitsAB_CE⟩

/-! ## 5. The possibilistic gap -/

/-- No classical causal model within the bilocality scenario, with ontic states in any
probability spaces, has exactly the support of the quantum statistics on the four tasks. The
statistics of a task cover all sixteen product states that the two sources can prepare, and not
only the four states of the task. -/
theorem gap {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB] :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ T sA sB xA xB y,
      (M.statistics sA sB T xA xB y = 0 ↔ Quantum.statistics sA sB T xA xB y = 0) :=
  Support.support_not_classical

/-- No classical causal model has exactly the support of the quantum statistics in the single
task `0+`. -/
theorem gap_in_one_task {ΛA ΛB : Type*} [MeasurableSpace ΛA] [MeasurableSpace ΛB] :
    ¬ ∃ M : General.Model ΛA ΛB, ∀ sA sB xA xB y,
      (M.statistics sA sB ![0, 0] xA xB y = 0 ↔
        Quantum.statistics sA sB ![0, 0] xA xB y = 0) :=
  Support.support_not_classical_one_task

/-- Every impossible event of the quantum statistics is an impossible event of the two-bit model.
So the gap uses the possible events as well as the impossible ones. -/
theorem has_every_impossible_event (T : Task) (sA sB xA xB : Fin 2) (y : Outcome)
    (h : Quantum.statistics sA sB T xA xB y = 0) :
    twoBits.statistics sA sB T xA xB y = 0 :=
  Support.twoBits_impossible_events T sA sB xA xB y h

/-- In the task `0+`, the event that the state `|0⟩|0⟩` is prepared and the outcome is `Y3` has
probability 1/16 in the quantum statistics, one quarter for the state times one quarter for the
outcome. It has probability zero in the two-bit model. -/
theorem example_00 :
    Quantum.statistics 0 0 ![0, 0] 0 0 Y3 = 1 / 16 ∧ twoBits.statistics 0 0 ![0, 0] 0 0 Y3 = 0 :=
  ⟨Support.quantum_state00.2, Support.twoBits_state00.2⟩

/-! ## 6. The quantum experiment -/

/-- Quantum theory reaches CE = 1, as the paper says. -/
theorem quantum_CE4 : CE4 Quantum.statistics = 1 := Quantum.CE4_statistics

/-- The paper's four measurements are the PBR measurement with its outcomes renamed. -/
theorem one_measurement (T : Task) (y : Outcome) :
    Quantum.effect T y = Quantum.pbr (relabel T y) := Quantum.effect_eq_pbr T y

/-- Two Bell pairs with steering, as Appendix C realizes each multi-source, give the quantum
statistics. -/
theorem bell_pairs : Quantum.bellModel.statistics = Quantum.statistics :=
  Quantum.bellModel_statistics

end

end PBRExclusion.Results
