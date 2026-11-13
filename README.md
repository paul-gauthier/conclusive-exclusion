# Conclusive exclusion in the bilocality scenario, checked in Lean

This is a Lean 4 library, built on Mathlib, about Yīng, Schmid and Spekkens, "A contextual advantage for conclusive exclusion: repurposing the Pusey-Barrett-Rudolph construction", [arXiv:2512.04173](https://arxiv.org/abs/2512.04173) (version 5). Equation numbers are those of the paper's PDF, and the library uses the paper's symbols where Lean allows.

## What agrees with the paper

The library checks these statements of the paper.

- Inequality (12) holds for the ontological model of Appendix B. When both qubits have the same four distributions μ and these satisfy the ontological identity (B4), CE is at most 15/16. The steps (B8) and (B40) are the theorems `eq_B8` and `eq_B40`, and the bound is tight, as the paper shows in (B42). The ontic state space is finite in these statements.
- Quantum theory reaches CE = 1. The operational identity of Eq. (9) holds, and in each task the outcome never occurs on the state that it excludes.
- Appendix C realizes each multi-source by steering on an entangled state. With two Bell pairs this gives the statistics of the quantum experiment.
- In a classical causal model each multi-source is a source, which emits an ontic state and reports an outcome under its setting. The ontological identity holds at each source whose outcomes are unbiased, which means that each outcome has probability 1/2 under each setting. This is the constraint that Appendix C states for a classical causal model with the causal structure of the bilocality scenario.

## A classical causal model with CE = 1

Appendix C concludes that inequality (12) is also a causal compatibility inequality for the bilocality scenario, one that follows for any classical causal model with that causal structure. The library has a classical causal model within that scenario, the two-bit model, whose CE is 1 on the paper's four tasks.

The two sources emit independent uniform bits, λ<sub>A</sub> and λ<sub>B</sub>. The outcomes are X<sub>A</sub> = λ<sub>A</sub> and X<sub>B</sub> = λ<sub>B</sub> ⊕ S<sub>B</sub>. In the task T = ab, with + read as 0 and − as 1, the joint measurement gives Y = 2 if λ<sub>A</sub> ⊕ λ<sub>B</sub> ⊕ a ⊕ b = 0 and Y = 3 otherwise.

The state ρ<sub>2|T</sub> then always gives Y = 3, the state ρ<sub>3|T</sub> always gives Y = 2, and Y is never 1 or 4. So the outcome is never the index of the prepared state, and CE<sub>T</sub> = 1 for every T. Each outcome of each source has probability 1/2 under each setting, as in the quantum experiment.

## What the causal structure requires, and what Appendices A and B use

The ontological identity holds at each source of the two-bit model. Source A gives |0⟩ and |+⟩ the same distribution, so Λ<sub>0</sub> = Λ<sub>+</sub> at that source, and source B gives |0⟩ and |−⟩ the same distribution. Appendix A cites Λ<sub>0</sub> ≠ Λ<sub>+</sub> for a noncontextual model, and the causal structure of the bilocality scenario does not require it.

In the paper's prepare-measure scenario both qubits are prepared in the same states, and Appendix B gives a state the same distribution on each, with Λ<sub>A</sub> × Λ<sub>B</sub> = Λ × Λ. That is how (B8) has the square of β<sub>T</sub>. In the bilocality scenario a classical causal model has a source for each qubit, and the two sources of the two-bit model give |+⟩ different distributions. With a μ for each source, the step of (B8) gives the product of the two sources' β<sub>T</sub>, and in the two-bit model one of the two is zero in each task.

When the two sources are independent copies of one source with unbiased outcomes, CE is at most 15/16 in the bilocality scenario, whatever the joint measurement. That is proved for ontic states in any probability space.

The library also has these statements in the form of Appendix B, for an ontological model with distributions for each qubit. Inequality (12) holds for such a model when each qubit satisfies the ontological identity and the two qubits have the same β<sub>T</sub> in every task, which includes the model of Appendix B. The two-bit model in this form satisfies the ontological identity on each qubit and has CE<sub>T</sub> = 1 in each task.

## The possibilistic gap

The paper concludes that the bilocality scenario has a possibilistic quantum-classical gap, and it argues from perfect conclusive exclusion. The library proves a possibilistic gap by another route. No classical causal model within the scenario has exactly the support of the quantum statistics on the four tasks, and this holds already in the single task 0+.

An event is a setting for each source, a task and the three outcomes, and an impossible event of some statistics is an event of probability zero. The proof uses the possible events as well as the impossible ones, because every impossible event of the quantum statistics is an impossible event of the two-bit model.

## What is not formalized

- Noncontextuality is not formalized. The ontological identity (B4) is a hypothesis of inequality (12), and so is one μ for both qubits.
- Appendix A, on the ontic supports, is not formalized.
- The ontological model of Appendix B has a finite ontic state space here. The bound for two independent copies of one source, the step of (B8) for two sources, and the possibilistic gap are proved for ontic states in any probability spaces.
- Matrices are real. The Pauli Y enters only by conjugation, so the real matrix XZ serves in its place.

## Where to read

Start with [PBRExclusion/Results.lean](PBRExclusion/Results.lean). It restates the results in the order of this table, each proved in a few lines from the rest of the library. To read it you need the four definitions files, of which [PBRExclusion/Defs.lean](PBRExclusion/Defs.lean) is the main one.

| Result | Theorem in `PBRExclusion.Results` |
|---|---|
| Inequality (12) from the identity (B4), and its tightness | `inequality_12`, `inequality_12_tight` |
| The paper's (B8) and (B40) | `eq_B8`, `eq_B40` |
| The two sources of the two-bit model | `sources` |
| The rule of its joint measurement, and Y never 1 or 4 | `joint_measurement`, `never_Y1_or_Y4` |
| Its outcomes are unbiased, and each state has probability 1/4 | `unbiased`, `prepared` |
| ρ<sub>2\|T</sub> gives Y = 3, and ρ<sub>3\|T</sub> gives Y = 2 | `state_2`, `state_3` |
| The outcome is never the index of the prepared state | `never_excludes_the_prepared_state` |
| CE<sub>T</sub> = 1 in each task, and CE = 1 | `CE_eq_one`, `CE4_eq_one` |
| The ontological identity holds at each source | `identity_A`, `identity_B` |
| Source A gives \|0⟩ and \|+⟩ the same distribution, and source B gives \|0⟩ and \|−⟩ the same one | `same_distribution_A`, `same_distribution_B` |
| The two sources give \|+⟩ different distributions | `different_distributions` |
| (B8) with the product of the two sources' β<sub>T</sub> | `product_of_β` |
| One of the two β<sub>T</sub> is zero in each task | `one_β_zero` |
| The same step for ontic states in any probability spaces | `product_of_joint_overlaps`, `square_of_one_joint_overlap` |
| 15/16 holds for two independent copies of one unbiased source | `bound_for_one_source` |
| Appendix B with distributions for each qubit | `eq_B8_for_two_qubits`, `inequality_12_for_equal_β`, `two_bits_in_this_form` |
| No classical causal model has exactly the quantum support | `gap`, `gap_in_one_task` |
| Every impossible event of the quantum statistics is impossible in the two-bit model | `has_every_impossible_event` |
| One event that quantum theory allows is impossible in the two-bit model | `example_00` |
| Quantum theory reaches CE = 1 | `quantum_CE4` |
| The four measurements are the PBR measurement with outcomes renamed | `one_measurement` |
| Two Bell pairs with steering give the quantum statistics | `bell_pairs` |

## From the paper's symbols to the library's

| Paper | Library |
|---|---|
| S<sub>A</sub>, S<sub>B</sub>, X<sub>A</sub>, X<sub>B</sub> | `sA sB xA xB : Fin 2`, with 0 for the Z-source and for the first state of a basis |
| T ∈ {0+, 0−, 1+, 1−} | `T : Task`, written `![0,0]`, `![0,1]`, `![1,0]`, `![1,1]` |
| Y ∈ {1, 2, 3, 4} | `Y1`, `Y2`, `Y3`, `Y4 : Outcome` |
| ℙ(X<sub>A</sub> X<sub>B</sub> Y \| S<sub>A</sub> S<sub>B</sub> T) | `P sA sB T xA xB y`, with `P : Statistics` |
| \|0⟩, \|1⟩, \|+⟩, \|−⟩ | `Quantum.state 0 0`, `state 0 1`, `state 1 0`, `state 1 1` |
| ρ<sub>Y\|T</sub>, Eqs. (2) and (4) | the setting and outcome `(i, T i)` on qubit A and `(j, T j)` on qubit B for `Y = (i, j)`, and `Quantum.task_state_eq` |
| \|φ<sub>Y\|0+</sub>⟩ and ℳ<sub>0+</sub>, Eq. (3) | `Quantum.pbrKet`, `Quantum.pbr` |
| E<sub>Y\|T</sub>, Eq. (5) | `Quantum.effect T y` |
| CE<sub>T</sub>, Eqs. (6) and (7) | `CE P T` |
| CE, Eq. (8) | `CE4 P` |
| The operational identity, Eq. (9) | `Quantum.state_identity` |
| Inequality (12) | `OntologicalModel.CE4_le` |
| Λ and λ | `Λ` and `l`, because Lean reserves λ |
| μ<sub>0</sub>, μ<sub>1</sub>, μ<sub>+</sub>, μ<sub>−</sub> | `N.μ 0 0`, `N.μ 0 1`, `N.μ 1 0`, `N.μ 1 1`, and `S.μ s x` for a source |
| ξ<sub>Y\|T</sub>(λ<sub>A</sub>, λ<sub>B</sub>) | `N.ξ T lA lB y` |
| The ontological identity (B4) | `OntologicalModel.Identity`, `Source.ontological_identity` |
| (B8), written in the paper for the task 0+ | `OntologicalModel.CE_le` |
| β<sub>T</sub>, (B14) and (B15) | `OntologicalModel.β`, `Source.β` |
| (B40) | `OntologicalModel.two_le_sum_β` |
| The tightness shown in (B42) | `exists_ontologicalModel_CE4_eq` |
| A multi-source | `Source`, which is a classical model of one |
| A classical causal model within the bilocality scenario | `Model`, and `General.Model` for ontic states in any probability space |
| The entangled states on A′A and BB′ with their multi-meters | `Quantum.bellModel`, with Bell pairs |

The library has two quantities of its own. The forbidden mass of a task adds up, over the task's four states, the probability that the state is prepared and the outcome excludes it, and with unbiased outcomes CE<sub>T</sub> is one minus the forbidden mass. The joint overlap of a source on a task is half of β<sub>T</sub> when the outcomes are unbiased, and it is defined without that assumption.

## Build and check

You need [elan](https://github.com/leanprover/elan), which installs the Lean version named in `lean-toolchain`.

```bash
lake exe cache get
lake build
lake env lean scripts/axioms.lean
```

The first command downloads Mathlib's compiled files. The second builds the library. The third checks every theorem of the library, and fails if one depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, the three that Lean and Mathlib use throughout. A `sorry` would show up there as the axiom `sorryAx`.

## Layout

Each statements file gives every statement with the name of its proof after `:=`, so it can be read without the proofs.

| File | Contents |
|---|---|
| `PBRExclusion/Results.lean` | The main results, in order |
| `PBRExclusion/Defs.lean` | Tasks, statistics, CE, classical causal models and ontological models with finite ontic state spaces, the two-bit model |
| `PBRExclusion/Statements.lean` | Appendix B, the ontological identity on a source, the steps of Appendix B for two sources, the two sources of the two-bit model |
| `PBRExclusion/GeneralDefs.lean`, `GeneralStatements.lean` | Classical causal models with ontic states in any probability space, and the bound for two independent copies of one source |
| `PBRExclusion/QuantumDefs.lean`, `QuantumStatements.lean` | The four states, the PBR measurement, the four tasks' measurements and their statistics |
| `PBRExclusion/NetworkDefs.lean`, `NetworkStatements.lean` | The same experiment with two Bell pairs and steering |
| `PBRExclusion/SupportStatements.lean` | The two-bit model's CE and impossible events, and the support of the quantum statistics |
| `PBRExclusion/Proofs/` | The proofs |
| `scripts/axioms.lean` | The check of axioms |
