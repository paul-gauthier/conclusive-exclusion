import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import PBRExclusion.Proofs.Examples

/-!
# Proofs for Appendix B, in the paper's form and with sources

This file proves the paper's inequality (12) for an `OntologicalModel` and its tightness, the
ontological identity on an unbiased source, the two statements that relate an ontological model
to a classical causal model with one source for both qubits, and the statements about
distributions for each qubit. The statements are in
`PBRExclusion/Statements.lean`.
-/

namespace PBRExclusion.Proofs

noncomputable section

variable {Λ : Type*} [Fintype Λ]

/-- A setting is `0` or `1`. -/
theorem fin_two_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  fin_cases s <;> simp

/-! ## The paper's inequality (12) -/

/-- This is the paper's (B40). Given the ontological identity (B4), the four `β_T` sum to at least
2. -/
theorem two_le_sum_β (N : OntologicalModel Λ) (h : N.Identity) : 2 ≤ ∑ T : Task, N.β T := by
  have h1 := sum_le_sum_min N.μ N.μ_nonneg fun l => by
    have := h l
    linarith
  have h2 : ∑ l, (N.μ 0 0 l + N.μ 0 1 l) = 2 := by
    rw [Finset.sum_add_distrib, N.μ_sum, N.μ_sum]
    norm_num
  unfold OntologicalModel.β
  linarith

/-- This is the paper's (B8). The states that the outcomes of the task `T` exclude carry weight at
least `β_T` squared, and the square is there because both qubits have the same four distributions.
-/
theorem β_sq_le (N : OntologicalModel Λ) (T : Task) :
    N.β T ^ 2 ≤
      ∑ i, ∑ j, ∑ lA, ∑ lB, N.μ i (T i) lA * N.μ j (T j) lB * N.ξ T lA lB (i, j) := by
  rw [sq]
  exact sum_min_mul_sum_min_le (fun i l => N.μ i (T i) l) (fun j l => N.μ j (T j) l) (N.ξ T)
    (fun _ _ => N.μ_nonneg _ _ _) (fun _ _ => N.μ_nonneg _ _ _) (N.ξ_nonneg T) (N.ξ_sum T)

theorem ontological_CE4_le (N : OntologicalModel Λ) (h : N.Identity) : N.CE4 ≤ 15 / 16 := by
  have h1 := two_le_sum_β N h
  have h2 := sq_sum_le_four_mul_sum_sq N.β
  have h3 : ∑ T : Task, N.β T ^ 2 ≤ ∑ T : Task, 4 * (1 - N.CE T) :=
    Finset.sum_le_sum fun T _ => by
      have := β_sq_le N T
      unfold OntologicalModel.CE
      linarith
  have h4 : ∑ T : Task, 4 * (1 - N.CE T) = 16 - 16 * N.CE4 := by
    unfold OntologicalModel.CE4
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_pair_one]
    ring
  nlinarith [sq_nonneg ((∑ T : Task, N.β T) - 2)]

/-! ## The toy bit as an ontological model -/

theorem toyOntological_identity : toyOntological.Identity := by
  intro l
  simp only [toyOntological]
  generalize l 0 = a
  generalize l 1 = b
  fin_cases a <;> fin_cases b <;> simp

/-- The toy bit has CE 15/16 in each task. -/
theorem toyOntological_CE (T : Task) : toyOntological.CE T = 15 / 16 := by
  have h : ∀ i j : Fin 2,
      ∑ lA : Pair, ∑ lB : Pair,
          toyOntological.μ i (T i) lA * toyOntological.μ j (T j) lB *
            toyOntological.ξ T lA lB (i, j) =
        4 * toy.statistics i j T (T i) (T j) (i, j) := by
    intro i j
    simp only [toyOntological, toy, Model.statistics, avoiding, DetSource.toSource, toyBit,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
    by_cases hA : lA i = T i <;> by_cases hB : lB j = T j <;>
      by_cases hy : (avoid lA T, avoid lB T) = (i, j) <;> simp [hA, hB, hy]
    norm_num
  have hF : forbidden toy.statistics T = 1 / 16 := by
    unfold toy
    rw [forbidden_avoiding_eq, toyBit_jointOverlap]
    norm_num
  unfold forbidden at hF
  unfold OntologicalModel.CE
  simp_rw [h, ← Finset.mul_sum]
  rw [hF]
  norm_num

theorem toyOntological_CE4 : toyOntological.CE4 = 15 / 16 := by
  unfold OntologicalModel.CE4
  simp_rw [toyOntological_CE]
  rw [sum_pair]
  norm_num

theorem exists_ontologicalModel_CE4_eq :
    ∃ N : OntologicalModel Pair, N.Identity ∧ N.CE4 = 15 / 16 :=
  ⟨toyOntological, toyOntological_identity, toyOntological_CE4⟩

/-! ## An unbiased source satisfies the ontological identity (B4) -/

/-- Both sides of the identity are the source's own distribution `p l`. -/
theorem μ_identity (S : Source Λ) (h : S.Unbiased) (l : Λ) :
    1 / 2 * S.μ 0 0 l + 1 / 2 * S.μ 0 1 l =
      1 / 2 * S.μ 1 0 l + 1 / 2 * S.μ 1 1 l := by
  have h0 := S.resp_sum 0 l
  have h1 := S.resp_sum 1 l
  rw [Fin.sum_univ_two] at h0 h1
  simp only [Source.μ, h 0 0, h 0 1, h 1 0, h 1 1]
  linear_combination S.p l * (h0 - h1)

/-! ## One unbiased source for both qubits is an ontological model of Appendix B -/

/-- The ontological model of Appendix B that a classical causal model gives when its source A is
unbiased. The four distributions are source A's `μ`, and the response function is the model's. -/
def ontologicalOfModel (M : Model Λ Λ) (hU : M.A.Unbiased) : OntologicalModel Λ where
  μ s x l := M.A.μ s x l
  ξ T := M.ξ T
  μ_nonneg s x l :=
    div_nonneg (mul_nonneg (M.A.p_nonneg l) (M.A.resp_nonneg s l x)) (marginal_nonneg _ _ _)
  μ_sum s x := by
    simp only [Source.μ]
    rw [← Finset.sum_div]
    change M.A.marginal s x / M.A.marginal s x = 1
    rw [hU s x]
    norm_num
  ξ_nonneg T := M.ξ_nonneg T
  ξ_sum T := M.ξ_sum T

/-- That ontological model has the classical causal model's CE in each task. -/
theorem ontologicalOfModel_CE (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) (T : Task) :
    (ontologicalOfModel M hU).CE T = CE M.statistics T := by
  rw [CE_eq_of_unbiased M hU (h ▸ hU)]
  simp only [OntologicalModel.CE, ontologicalOfModel, forbidden, Model.statistics, Source.μ,
    hU _ _, ← h]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
  ring

theorem exists_ontologicalModel (M : Model Λ Λ) (h : M.A = M.B) (hU : M.A.Unbiased) :
    ∃ N : OntologicalModel Λ, N.Identity ∧ (∀ s x l, N.μ s x l = M.A.μ s x l) ∧
      ∀ T, N.CE T = CE M.statistics T :=
  ⟨ontologicalOfModel M hU, fun l => μ_identity M.A hU l, fun _ _ _ => rfl,
    ontologicalOfModel_CE M h hU⟩

/-- `sourceOfOntological N h` is the source of an ontological model of Appendix B. It emits the
average distribution of (B4) and reports its outcome by Bayes' rule. Where the average is zero the
outcome is a fair coin, and no ontic state of positive probability uses that choice. -/
def sourceOfOntological (N : OntologicalModel Λ) (h : N.Identity) : Source Λ where
  p l := 1 / 2 * N.μ 0 0 l + 1 / 2 * N.μ 0 1 l
  resp s l x :=
    if N.μ 0 0 l + N.μ 0 1 l = 0 then 1 / 2 else N.μ s x l / (N.μ 0 0 l + N.μ 0 1 l)
  p_nonneg l :=
    add_nonneg (mul_nonneg (by norm_num) (N.μ_nonneg 0 0 l))
      (mul_nonneg (by norm_num) (N.μ_nonneg 0 1 l))
  p_sum := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, N.μ_sum, N.μ_sum]
    norm_num
  resp_nonneg s l x := by
    split_ifs
    · norm_num
    · exact div_nonneg (N.μ_nonneg _ _ _) (add_nonneg (N.μ_nonneg _ _ _) (N.μ_nonneg _ _ _))
  resp_sum s l := by
    rw [Fin.sum_univ_two]
    split_ifs with h0
    · norm_num
    · have hs : N.μ s 0 l + N.μ s 1 l = N.μ 0 0 l + N.μ 0 1 l := by
        have hI := h l
        obtain rfl | rfl := fin_two_cases s
        · rfl
        · linarith
      rw [← add_div, hs]
      exact div_self h0

/-- The joint weight of an ontic state and an outcome is half of the paper's distribution. -/
theorem sourceOfOntological_p_mul_resp (N : OntologicalModel Λ) (h : N.Identity) (s x : Fin 2)
    (l : Λ) :
    (sourceOfOntological N h).p l * (sourceOfOntological N h).resp s l x = 1 / 2 * N.μ s x l := by
  have h00 := N.μ_nonneg 0 0 l
  have h01 := N.μ_nonneg 0 1 l
  have h10 := N.μ_nonneg 1 0 l
  have h11 := N.μ_nonneg 1 1 l
  have hI := h l
  simp only [sourceOfOntological]
  split_ifs with h0
  · have hz : N.μ s x l = 0 := by
      obtain rfl | rfl := fin_two_cases s <;> obtain rfl | rfl := fin_two_cases x <;> linarith
    have hp : 1 / 2 * N.μ 0 0 l + 1 / 2 * N.μ 0 1 l = 0 := by linarith
    rw [hp, hz]
    ring
  · field_simp

theorem sourceOfOntological_unbiased (N : OntologicalModel Λ) (h : N.Identity) :
    (sourceOfOntological N h).Unbiased := by
  intro s x
  unfold Source.marginal
  simp_rw [sourceOfOntological_p_mul_resp, ← Finset.mul_sum, N.μ_sum, mul_one]

theorem sourceOfOntological_μ (N : OntologicalModel Λ) (h : N.Identity) (s x : Fin 2) (l : Λ) :
    (sourceOfOntological N h).μ s x l = N.μ s x l := by
  unfold Source.μ
  rw [sourceOfOntological_unbiased N h s x, sourceOfOntological_p_mul_resp]
  ring

/-- `modelOfOntological N h` is the classical causal model with two independent copies of that
source and the ontological model's response function. -/
def modelOfOntological (N : OntologicalModel Λ) (h : N.Identity) : Model Λ Λ where
  A := sourceOfOntological N h
  B := sourceOfOntological N h
  ξ T := N.ξ T
  ξ_nonneg T := N.ξ_nonneg T
  ξ_sum T := N.ξ_sum T

/-- That classical causal model has the ontological model's CE in each task. -/
theorem modelOfOntological_CE (N : OntologicalModel Λ) (h : N.Identity) (T : Task) :
    CE (modelOfOntological N h).statistics T = N.CE T := by
  rw [CE_eq_of_unbiased _ (sourceOfOntological_unbiased N h) (sourceOfOntological_unbiased N h)]
  simp only [OntologicalModel.CE, forbidden, Model.statistics, modelOfOntological]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
  have hA := sourceOfOntological_p_mul_resp N h i (T i) lA
  have hB := sourceOfOntological_p_mul_resp N h j (T j) lB
  linear_combination
    ((sourceOfOntological N h).p lB * (sourceOfOntological N h).resp j lB (T j) * hA +
    1 / 2 * N.μ i (T i) lA * hB) * N.ξ T lA lB (i, j)

theorem ontological_exists_model (N : OntologicalModel Λ) (h : N.Identity) :
    ∃ M : Model Λ Λ, M.A = M.B ∧ M.A.Unbiased ∧ (∀ s x l, M.A.μ s x l = N.μ s x l) ∧
      ∀ T, CE M.statistics T = N.CE T :=
  ⟨modelOfOntological N h, rfl, sourceOfOntological_unbiased N h, sourceOfOntological_μ N h,
    modelOfOntological_CE N h⟩

/-! ## The paper's (B8) and Appendix B with distributions for each qubit -/

variable {ΛA ΛB : Type*} [Fintype ΛA] [Fintype ΛB]

theorem ontological_CE_le (N : OntologicalModel Λ) (T : Task) : N.CE T ≤ 1 - 1 / 4 * N.β T ^ 2 := by
  have := β_sq_le N T
  unfold OntologicalModel.CE
  linarith

theorem ab_CE_le (N : OntologicalModelAB ΛA ΛB) (T : Task) :
    N.CE T ≤ 1 - 1 / 4 * (N.βA T * N.βB T) := by
  have := sum_min_mul_sum_min_le (fun i l => N.μA i (T i) l) (fun j l => N.μB j (T j) l) (N.ξ T)
    (fun _ _ => N.μA_nonneg _ _ _) (fun _ _ => N.μB_nonneg _ _ _) (N.ξ_nonneg T) (N.ξ_sum T)
  unfold OntologicalModelAB.CE OntologicalModelAB.βA OntologicalModelAB.βB
  linarith

def abOfModel (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    OntologicalModelAB ΛA ΛB where
  μA s x l := M.A.μ s x l
  μB s x l := M.B.μ s x l
  ξ T := M.ξ T
  μA_nonneg s x l :=
    div_nonneg (mul_nonneg (M.A.p_nonneg l) (M.A.resp_nonneg s l x)) (marginal_nonneg _ _ _)
  μA_sum s x := by
    simp only [Source.μ]
    rw [← Finset.sum_div]
    change M.A.marginal s x / M.A.marginal s x = 1
    rw [hA s x]
    norm_num
  μB_nonneg s x l :=
    div_nonneg (mul_nonneg (M.B.p_nonneg l) (M.B.resp_nonneg s l x)) (marginal_nonneg _ _ _)
  μB_sum s x := by
    simp only [Source.μ]
    rw [← Finset.sum_div]
    change M.B.marginal s x / M.B.marginal s x = 1
    rw [hB s x]
    norm_num
  ξ_nonneg T := M.ξ_nonneg T
  ξ_sum T := M.ξ_sum T

theorem abOfModel_CE (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) (T : Task) :
    (abOfModel M hA hB).CE T = CE M.statistics T := by
  rw [CE_eq_of_unbiased M hA hB]
  simp only [OntologicalModelAB.CE, abOfModel, forbidden, Model.statistics, Source.μ, hA _ _,
    hB _ _]
  congr 1
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun lA _ => Finset.sum_congr rfl fun lB _ => ?_
  ring

theorem exists_ontologicalModelAB (M : Model ΛA ΛB) (hA : M.A.Unbiased) (hB : M.B.Unbiased) :
    ∃ N : OntologicalModelAB ΛA ΛB, N.Identity ∧ (∀ s x l, N.μA s x l = M.A.μ s x l) ∧
      (∀ s x l, N.μB s x l = M.B.μ s x l) ∧ (∀ T lA lB y, N.ξ T lA lB y = M.ξ T lA lB y) ∧
      ∀ T, N.CE T = CE M.statistics T :=
  ⟨abOfModel M hA hB, ⟨fun l => μ_identity M.A hA l, fun l => μ_identity M.B hB l⟩,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, abOfModel_CE M hA hB⟩

theorem toAB_CE (N : OntologicalModel Λ) (T : Task) : N.toAB.CE T = N.CE T := rfl

theorem toAB_identity (N : OntologicalModel Λ) (h : N.Identity) : N.toAB.Identity := ⟨h, h⟩

theorem toAB_β (N : OntologicalModel Λ) (T : Task) :
    N.toAB.βA T = N.β T ∧ N.toAB.βB T = N.β T := ⟨rfl, rfl⟩

theorem two_le_sum_βA (N : OntologicalModelAB ΛA ΛB) (h : N.Identity) : 2 ≤ ∑ T : Task, N.βA T := by
  have h1 := sum_le_sum_min N.μA N.μA_nonneg fun l => by
    have := h.1 l
    linarith
  have h2 : ∑ l, (N.μA 0 0 l + N.μA 0 1 l) = 2 := by
    rw [Finset.sum_add_distrib, N.μA_sum, N.μA_sum]
    norm_num
  unfold OntologicalModelAB.βA
  linarith

theorem ab_CE4_le (N : OntologicalModelAB ΛA ΛB) (h : N.Identity) (hβ : ∀ T, N.βA T = N.βB T) :
    N.CE4 ≤ 15 / 16 := by
  have h1 := two_le_sum_βA N h
  have h2 := sq_sum_le_four_mul_sum_sq N.βA
  have h3 : ∑ T : Task, N.βA T ^ 2 ≤ ∑ T : Task, 4 * (1 - N.CE T) :=
    Finset.sum_le_sum fun T _ => by
      have := ab_CE_le N T
      rw [← hβ T] at this
      nlinarith
  have h4 : ∑ T : Task, 4 * (1 - N.CE T) = 16 - 16 * N.CE4 := by
    unfold OntologicalModelAB.CE4
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_pair_one]
    ring
  nlinarith [sq_nonneg ((∑ T : Task, N.βA T) - 2)]

end

end PBRExclusion.Proofs
