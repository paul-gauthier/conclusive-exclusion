import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PBRExclusion.GeneralStatements
import PBRExclusion.QuantumDefs

/-!
# Proofs for the quantum experiment

The statements are in `PBRExclusion/QuantumStatements.lean`.

* `proj v` is symmetric and positive. For `v ≠ 0` it has trace one and squares to itself, and
  rotating it by an orthogonal matrix `U` gives `proj (U v)`.
* Born's rule on projectors is a squared inner product over norms (`born_proj`). So a probability
  is zero when two integer vectors are orthogonal.
* The Pauli of a pair moves labels (`pauli_conj_state`). Rotating a task's measurement and its
  states back by the task's own Paulis gives the task `0+` (`born_effect`), and so exclusion is
  perfect in every task.
* A Pauli on both qubits permutes the PBR vectors up to a sign (`pauli_kron_pbrKet`), and so the
  paper's four measurements are the PBR measurement with its outcomes renamed.
-/

namespace PBRExclusion.Quantum.Proofs

open Matrix
open scoped Kronecker

noncomputable section

/-! ## Projectors -/

section Proj

variable {n m : Type*} [Fintype n] [Fintype m]

theorem dot_self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem proj_apply (v : n → ℝ) (a b : n) : proj v a b = (v ⬝ᵥ v)⁻¹ * (v a * v b) := by
  simp [proj, vecMulVec_apply]

theorem proj_posSemidef (v : n → ℝ) : (proj v).PosSemidef := by
  have h : (vecMulVec v (star v)).PosSemidef := posSemidef_vecMulVec_self_star v
  rw [star_trivial] at h
  exact h.smul (inv_nonneg.2 (dot_self_nonneg v))

theorem proj_trace {v : n → ℝ} (hv : v ⬝ᵥ v ≠ 0) : (proj v).trace = 1 := by
  simp [proj, trace_smul, hv]

theorem proj_mul_proj (u v : n → ℝ) :
    proj u * proj v = ((u ⬝ᵥ u)⁻¹ * (v ⬝ᵥ v)⁻¹ * (u ⬝ᵥ v)) • vecMulVec u v := by
  ext a b
  simp only [proj, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, Matrix.smul_apply,
    vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem proj_mul_self {v : n → ℝ} (hv : v ⬝ᵥ v ≠ 0) : proj v * proj v = proj v := by
  rw [proj_mul_proj, proj]
  congr 1
  field_simp

theorem proj_mul_proj_of_orthogonal {u v : n → ℝ} (h : u ⬝ᵥ v = 0) : proj u * proj v = 0 := by
  rw [proj_mul_proj, h]
  simp

/-- Rotating a projector by an orthogonal matrix gives the projector of the rotated vector. -/
theorem proj_conj [DecidableEq n] (U : Matrix m n ℝ) (hU : Uᵀ * U = 1) (v : n → ℝ) :
    U * proj v * Uᵀ = proj (U *ᵥ v) := by
  have hdot : (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]
  simp only [proj, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    hdot]

theorem trace_proj_mul_proj (u v : n → ℝ) :
    (proj u * proj v).trace = (u ⬝ᵥ v) ^ 2 / ((u ⬝ᵥ u) * (v ⬝ᵥ v)) := by
  rw [proj_mul_proj, trace_smul, trace_vecMulVec, smul_eq_mul]
  ring

end Proj

theorem tensor_dot_tensor (a b c d : Fin 2 → ℝ) :
    tensor a b ⬝ᵥ tensor c d = (a ⬝ᵥ c) * (b ⬝ᵥ d) := by
  simp only [dotProduct, tensor, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem proj_kronecker (a b : Fin 2 → ℝ) : proj a ⊗ₖ proj b = proj (tensor a b) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [kroneckerMap_apply, proj_apply, tensor_dot_tensor, tensor]
  ring

/-- Born's rule on projectors is a squared inner product divided by the squared norms. -/
theorem born_proj (w : TwoQubits → ℝ) (a b : Fin 2 → ℝ) :
    born (proj w) (proj a) (proj b) =
      (w ⬝ᵥ tensor a b) ^ 2 / ((w ⬝ᵥ w) * ((a ⬝ᵥ a) * (b ⬝ᵥ b))) := by
  rw [born, proj_kronecker, trace_proj_mul_proj, tensor_dot_tensor]

/-! ## Cases -/

/-- A task is the list of its two values. -/
theorem pair_eq (T : Task) : T = ![T 0, T 1] := by
  ext i
  fin_cases i <;> rfl

/-- To prove something of every task, prove it of the four. -/
theorem forall_pair {p : Pair → Prop} (h00 : p ![0, 0]) (h01 : p ![0, 1]) (h10 : p ![1, 0])
    (h11 : p ![1, 1]) (T : Task) : p T := by
  rw [pair_eq T]
  generalize T 0 = a
  generalize T 1 = b
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ## The four states -/

theorem ket_dot_ket (s x x' : Fin 2) :
    ket s x ⬝ᵥ ket s x' = if x = x' then (if s = 0 then 1 else 2) else 0 := by
  fin_cases s <;> fin_cases x <;> fin_cases x' <;> simp [ket, dotProduct, Fin.sum_univ_two] <;>
    norm_num

theorem ket_dot_self_ne_zero (s x : Fin 2) : ket s x ⬝ᵥ ket s x ≠ 0 := by
  simp only [ket_dot_ket, ↓reduceIte]
  split_ifs <;> norm_num

theorem state_eq :
    state 0 0 = !![1, 0; 0, 0] ∧ state 0 1 = !![0, 0; 0, 1] ∧
      state 1 0 = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] ∧
      state 1 1 = !![1 / 2, -1 / 2; -1 / 2, 1 / 2] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [state, proj_apply, ket, dotProduct, Fin.sum_univ_two] <;> norm_num

theorem state_posSemidef (s x : Fin 2) : (state s x).PosSemidef := proj_posSemidef _

theorem state_trace (s x : Fin 2) : (state s x).trace = 1 := proj_trace (ket_dot_self_ne_zero s x)

theorem state_mul_self (s x : Fin 2) : state s x * state s x = state s x :=
  proj_mul_self (ket_dot_self_ne_zero s x)

theorem state_identity :
    (1 / 2 : ℝ) • state 0 0 + (1 / 2 : ℝ) • state 0 1 =
      (1 / 2 : ℝ) • state 1 0 + (1 / 2 : ℝ) • state 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := state_eq
  rw [h00, h01, h10, h11]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> norm_num

/-! ## The PBR measurement -/

theorem pbrKet_eq :
    (pbrKet (0, 0) = fun k => (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (0, 1) = fun k => (!![1, -1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (1, 0) = fun k => (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) ∧
      (pbrKet (1, 1) = fun k => (!![2, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℝ) k.1 k.2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext ⟨a, b⟩ <;> fin_cases a <;> fin_cases b <;>
    simp [pbrKet, tensor, ket] <;> norm_num

theorem pbrKet_dot_pbrKet (y z : Outcome) :
    pbrKet y ⬝ᵥ pbrKet z =
      if y = z then (if y = (0, 0) then 2 else if y = (1, 1) then 8 else 4) else 0 := by
  obtain ⟨i, j⟩ := y
  obtain ⟨k, l⟩ := z
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [pbrKet, tensor, ket, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

theorem pbrKet_dot_self_ne_zero (y : Outcome) : pbrKet y ⬝ᵥ pbrKet y ≠ 0 := by
  simp only [pbrKet_dot_pbrKet, ↓reduceIte]
  split_ifs <;> norm_num

theorem pbr_posSemidef (y : Outcome) : (pbr y).PosSemidef := proj_posSemidef _

theorem pbr_mul_pbr (y z : Outcome) : pbr y * pbr z = if y = z then pbr y else 0 := by
  by_cases h : y = z
  · subst h
    simp only [↓reduceIte]
    exact proj_mul_self (pbrKet_dot_self_ne_zero y)
  · simp only [h, ↓reduceIte]
    exact proj_mul_proj_of_orthogonal (by simp only [pbrKet_dot_pbrKet, h, ↓reduceIte])

theorem pbr_sum : ∑ y, pbr y = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.sum_apply, pbr, proj_apply, pbrKet_dot_pbrKet, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pbrKet, tensor, ket] <;> norm_num

/-! ## The Paulis and the states of a task -/

theorem pauli_eq :
    pauli ![0, 0] = 1 ∧ pauli ![0, 1] = pauliZ ∧ pauli ![1, 0] = pauliX ∧
      pauli ![1, 1] = !![0, -1; 1, 0] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [pauli, pauliX, pauliZ]

theorem pauli_mul_transpose (T : Task) : pauli T * (pauli T)ᵀ = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := pauli_eq
  refine forall_pair (p := fun T => pauli T * (pauli T)ᵀ = 1) ?_ ?_ ?_ ?_ T
  · rw [h00]; simp
  all_goals
    first | rw [h01] | rw [h10] | rw [h11]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_transpose_mul (T : Task) : (pauli T)ᵀ * pauli T = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := pauli_eq
  refine forall_pair (p := fun T => (pauli T)ᵀ * pauli T = 1) ?_ ?_ ?_ ?_ T
  · rw [h00]; simp
  all_goals
    first | rw [h01] | rw [h10] | rw [h11]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli_conj_state (T : Task) (s x : Fin 2) :
    pauli T * state s x * (pauli T)ᵀ = state s (x + T s) := by
  obtain ⟨h00, h01, h10, h11⟩ := pauli_eq
  obtain ⟨s00, s01, s10, s11⟩ := state_eq
  revert s x
  refine forall_pair
    (p := fun T => ∀ s x : Fin 2, pauli T * state s x * (pauli T)ᵀ = state s (x + T s))
    ?_ ?_ ?_ ?_ T <;> intro s x <;> fin_cases s <;> fin_cases x <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
      simp [h00, h01, h10, h11, s00, s01, s10, s11, pauliX, pauliZ, Matrix.mul_apply,
        Fin.sum_univ_two] <;> norm_num)

theorem pauli_kron_transpose_mul (τA τB : Pair) :
    (pauli τA ⊗ₖ pauli τB)ᵀ * (pauli τA ⊗ₖ pauli τB) = 1 := by
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, pauli_transpose_mul, pauli_transpose_mul,
    one_kronecker_one]

theorem pauli_kron_mul_transpose (τA τB : Pair) :
    (pauli τA ⊗ₖ pauli τB) * (pauli τA ⊗ₖ pauli τB)ᵀ = 1 := by
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, pauli_mul_transpose, pauli_mul_transpose,
    one_kronecker_one]

theorem task_state_eq (T : Task) (i j : Fin 2) :
    (pauli T ⊗ₖ pauli T) * (state i 0 ⊗ₖ state j 0) * (pauli T ⊗ₖ pauli T)ᵀ =
      state i (T i) ⊗ₖ state j (T j) := by
  rw [← kroneckerMap_transpose, ← mul_kronecker_mul, ← mul_kronecker_mul, pauli_conj_state,
    pauli_conj_state, zero_add, zero_add]

/-! ## The measurement of a task -/

theorem effect_eq_proj (T : Task) (y : Outcome) :
    effect T y = proj ((pauli T ⊗ₖ pauli T) *ᵥ pbrKet y) :=
  proj_conj _ (pauli_kron_transpose_mul T T) _

theorem effect_posSemidef (T : Task) (y : Outcome) : (effect T y).PosSemidef := by
  rw [effect_eq_proj]
  exact proj_posSemidef _

theorem effect_sum (T : Task) : ∑ y, effect T y = 1 := by
  simp only [effect]
  rw [← Finset.sum_mul, ← Finset.mul_sum, pbr_sum, Matrix.mul_one, pauli_kron_mul_transpose]

theorem relabel_relabel (T : Task) (y : Outcome) : relabel T (relabel T y) = y := by
  unfold relabel
  split_ifs <;> simp

/-! ## The statistics are a probability distribution -/

theorem born_proj_nonneg (w : TwoQubits → ℝ) (a b : Fin 2 → ℝ) :
    0 ≤ born (proj w) (proj a) (proj b) := by
  rw [born_proj]
  exact div_nonneg (sq_nonneg _)
    (mul_nonneg (dot_self_nonneg _) (mul_nonneg (dot_self_nonneg _) (dot_self_nonneg _)))

theorem statistics_nonneg (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) (y : Outcome) :
    0 ≤ statistics sA sB T xA xB y := by
  have h : 0 ≤ born (effect T y) (state sA xA) (state sB xB) := by
    rw [effect_eq_proj]
    exact born_proj_nonneg _ _ _
  unfold statistics
  positivity

theorem sum_statistics (sA sB : Fin 2) (T : Task) (xA xB : Fin 2) :
    ∑ y, statistics sA sB T xA xB y = 1 / 4 := by
  simp only [statistics, born]
  rw [← Finset.mul_sum, ← trace_sum, ← Finset.sum_mul, effect_sum, Matrix.one_mul, trace_kronecker,
    state_trace, state_trace]
  norm_num

theorem statistics_sum (sA sB : Fin 2) (T : Task) :
    ∑ xA, ∑ xB, ∑ y, statistics sA sB T xA xB y = 1 := by
  simp only [sum_statistics, Fin.sum_univ_two]
  norm_num

/-! ## The quantum value -/

/-- On the states of its own task, a task's measurement gives what the PBR measurement gives on the
states of the task `0+`. -/
theorem born_effect (T : Task) (z : Outcome) (i j : Fin 2) :
    born (effect T z) (state i (T i)) (state j (T j)) =
      born (pbr z) (state i 0) (state j 0) := by
  rw [born, born, ← task_state_eq T i j, effect]
  have h := pauli_kron_transpose_mul T T
  generalize pauli T ⊗ₖ pauli T = U at h ⊢
  generalize state i 0 ⊗ₖ state j 0 = ρ
  calc (U * pbr z * Uᵀ * (U * ρ * Uᵀ)).trace
      = (U * (pbr z * (Uᵀ * U) * ρ) * Uᵀ).trace := by simp only [Matrix.mul_assoc]
    _ = (Uᵀ * U * (pbr z * (Uᵀ * U) * ρ)).trace := by
        rw [trace_mul_comm, ← Matrix.mul_assoc]
    _ = (pbr z * ρ).trace := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem pbrKet_dot_tensor (i j : Fin 2) :
    pbrKet (i, j) ⬝ᵥ tensor (ket i 0) (ket j 0) = 0 := by
  simp only [pbrKet, add_dotProduct, tensor_dot_tensor, ket_dot_ket]
  simp

/-- In the task `0+` the PBR outcome `(i, j)` never occurs on the state that it excludes. -/
theorem born_pbr_zero (i j : Fin 2) : born (pbr (i, j)) (state i 0) (state j 0) = 0 := by
  rw [pbr, state, state, born_proj, pbrKet_dot_tensor]
  simp

theorem born_forbidden (T : Task) (i j : Fin 2) :
    born (effect T (i, j)) (state i (T i)) (state j (T j)) = 0 := by
  rw [born_effect, born_pbr_zero]

theorem statistics_forbidden (T : Task) (i j : Fin 2) :
    statistics i j T (T i) (T j) (i, j) = 0 := by
  simp [statistics, born_forbidden]

theorem forbidden_statistics (T : Task) : forbidden statistics T = 0 := by
  simp [forbidden, statistics_forbidden]

theorem F4_statistics : F4 statistics = 0 := by
  simp [F4, forbidden_statistics]

theorem CE_statistics (T : Task) : CE statistics T = 1 := by
  simp [CE, statistics_forbidden]

theorem CE4_statistics : CE4 statistics = 1 := by
  simp only [CE4, CE_statistics, sum_pair]
  norm_num

/-! ## The four measurements are the PBR measurement -/

theorem proj_smul {n : Type*} [Fintype n] {c : ℝ} (hc : c ≠ 0) (v : n → ℝ) :
    proj (c • v) = proj v := by
  ext a b
  simp only [proj_apply, smul_dotProduct, dotProduct_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hq : v ⬝ᵥ v = 0
  · simp [hq]
  · field_simp

/-- A Pauli on both qubits permutes the PBR vectors, up to a sign. -/
theorem pauli_kron_pbrKet (T : Task) (y : Outcome) :
    ∃ c : ℝ, c ≠ 0 ∧ (pauli T ⊗ₖ pauli T) *ᵥ pbrKet y = c • pbrKet (relabel T y) := by
  obtain ⟨h00, h01, h10, h11⟩ := pauli_eq
  obtain ⟨i, j⟩ := y
  revert i j
  refine forall_pair
    (p := fun T => ∀ i j : Fin 2, ∃ c : ℝ, c ≠ 0 ∧
      (pauli T ⊗ₖ pauli T) *ᵥ pbrKet (i, j) = c • pbrKet (relabel T (i, j)))
    ?_ ?_ ?_ ?_ T <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    first
    | (refine ⟨1, one_ne_zero, ?_⟩
       ext ⟨a, b⟩
       fin_cases a <;> fin_cases b <;>
         simp [h00, h01, h10, h11, pauliX, pauliZ, mulVec, dotProduct, Fintype.sum_prod_type,
           Fin.sum_univ_two, pbrKet, tensor, ket, relabel] <;> norm_num
       done)
    | (refine ⟨-1, by norm_num, ?_⟩
       ext ⟨a, b⟩
       fin_cases a <;> fin_cases b <;>
         simp [h01, h10, h11, pauliX, pauliZ, mulVec, dotProduct, Fintype.sum_prod_type,
           Fin.sum_univ_two, pbrKet, tensor, ket, relabel])

theorem effect_eq_pbr (T : Task) (y : Outcome) : effect T y = pbr (relabel T y) := by
  obtain ⟨c, hc, h⟩ := pauli_kron_pbrKet T y
  rw [effect_eq_proj]
  change proj ((pauli T ⊗ₖ pauli T) *ᵥ pbrKet y) = _
  rw [h, proj_smul hc, pbr]

/-! ## One impossible outcome for each product state -/

/-- This is the exclusion table of the PBR measurement, stated as a rule. -/
theorem pbrKet_dot_tensor_eq_zero_iff (z : Outcome) (sA xA sB xB : Fin 2) :
    pbrKet z ⬝ᵥ tensor (ket sA xA) (ket sB xB) = 0 ↔ z = (sA + xA + xB, sB + xA + xB) := by
  obtain ⟨i, j⟩ := z
  fin_cases i <;> fin_cases j <;> fin_cases sA <;> fin_cases xA <;> fin_cases sB <;>
    fin_cases xB <;>
    simp [pbrKet, tensor, ket, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem born_pbr_eq_zero_iff (z : Outcome) (sA xA sB xB : Fin 2) :
    born (pbr z) (state sA xA) (state sB xB) = 0 ↔ z = (sA + xA + xB, sB + xA + xB) := by
  have h : pbrKet z ⬝ᵥ pbrKet z * (ket sA xA ⬝ᵥ ket sA xA * (ket sB xB ⬝ᵥ ket sB xB)) ≠ 0 :=
    mul_ne_zero (pbrKet_dot_self_ne_zero z)
      (mul_ne_zero (ket_dot_self_ne_zero _ _) (ket_dot_self_ne_zero _ _))
  rw [pbr, state, state, born_proj, ← pbrKet_dot_tensor_eq_zero_iff, div_eq_zero_iff]
  constructor
  · rintro (h' | h')
    · exact (pow_eq_zero_iff two_ne_zero).1 h'
    · exact absurd h' h
  · intro h'
    left
    rw [h']
    norm_num

/-! ## Without the renaming -/

theorem born_pbr_control : born (pbr (0, 1)) (state 0 0) (state 1 1) = 1 / 2 := by
  rw [pbr, state, state, born_proj]
  simp [pbrKet, tensor, ket, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end

end PBRExclusion.Quantum.Proofs
