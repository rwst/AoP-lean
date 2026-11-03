<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-->

# Certifying the main theorems of the briefs with `lake comparator`

`lake comparator` (Lean's built-in successor of
[`leanprover/comparator`](https://github.com/leanprover/comparator)) checks a challenge against a
solution. For every theorem the configuration names it establishes that

1. the theorem in the solution proves **the same statement** as in the challenge, compared
   constant by constant over the whole definitional closure, definitions by value, not just by
   name;
2. its proof uses **no axiom** outside the configuration's `permitted_axioms`, here only
   `propext`, `Quot.sound` and `Classical.choice`;
3. the result is **accepted by the Lean kernel**.

It builds and exports both sides inside a `bwrap` sandbox, so `bubblewrap` must be installed. The
setup follows the paper lanes of Subspace-Theorems, with one change: the external comparator, its
`lake test` driver and `landrun` are replaced by `lake comparator`, which needs no dependency.

## Lanes

Each certified brief has a lane of its own in `briefs/<Brief>/comparator/`:

- `theorems.txt`, the certified theorems, one per line;
- `Challenge<Brief>.lean`, the statements of record, generated and never edited by hand;
- `Solution<Brief>.lean`, the hand-written re-export of the brief modules that prove them;
- `comparator.json`, the configuration, generated together with the challenge.

`lakefile.toml` declares the challenge and the solution as libraries of their own, with
`srcDir = "briefs/<Brief>/comparator"`. Neither is a default target and nothing imports them, so
`lake build` is unaffected. The brief's name is part of each module name because module names must
be unique across the project.

| brief | certified | Lean | challenge |
| --- | --- | --- | --- |
| The Born rule is equivalent to the von Neumann entropy | Theorem 9 | `BornRuleEntropy.two_conditions_imply_third` | 117 lines, 6 KiB |
| Classical uncertainty principle | Corollary 1, Theorem 2 (eqs. 3 and 5), the final remark | 7 theorems, see `theorems.txt` | 101 lines, 5 KiB |
| Physical vector spaces for quantum mechanics | Corollary 2, Example 3 (in `n` dimensions) and its Remark, Example 4, Theorem 5 ([B]COBS) | 6 theorems, see `theorems.txt` | 163 lines, 7 KiB |
| Directional vectors vs quantum state vectors | eqs. (1)–(3), linearity in terms of probability, half a turn, states as rays, the outcomes as opposite directions, completeness of the forms (1) and (3) | 13 theorems, see `theorems.txt` | 83 lines, 4 KiB |
| Superpositions correspond to multiple decompositions | Theorem 1 and its two directions (eqs. 3 and 4), eq. (2), the support argument, mixtures of independent states are not pure | 6 theorems, see `theorems.txt` | 73 lines, 4 KiB |
| Inconsistent convergence in Hilbert space | eqs. (2)–(5), the convergence of `eʲ` in `ℓ²`, the eigenstates `\|j⟩` alone have no limit | 7 theorems, see `theorems.txt` | 51 lines, 2 KiB |
| Projective measurements are equilibration processes | Theorem 1 (EQ-LIND, EQ-HS, EQ-KL ⇔ EQ-MEAS, eqs. 2–12) and eq. (13), in finite dimension and in any dimension | 10 theorems, see `theorems.txt` | 653 lines, 34 KiB |

Lanes are meant for the briefs whose `open-problems.tex` has no item marked
`[blocks verification]`: BornRuleEntropy, ClassicalUncertaintyPrinciple, EntropyTopology,
InconsistentConvergence, ProjectiveMeasurement, QuantumVectorSpaces, SchroedingerEvolution,
SchwartzMomentProblem, SchwartzNorms, SuperpositionAndLinearity, SuperpositionAndMultipleMixtures
and UnitaryEntropy.

## Running it

```sh
lake build
scripts/comparator.sh                    # every lane
scripts/comparator.sh BornRuleEntropy    # one lane
```

`scripts/comparator.sh` runs `lake comparator --config briefs/<Brief>/comparator/comparator.json`
for each lane in turn, with `LEAN_NUM_THREADS=3` unless set otherwise, and fails if any lane is
rejected.

## Adding a lane

1. Write `briefs/<Brief>/comparator/theorems.txt` and `Solution<Brief>.lean`, which imports the
   brief modules that own the certified theorems (see the BornRuleEntropy lane).
2. Add the two libraries to `lakefile.toml`, after the brief's own library.
3. Generate the challenge and the configuration, build both sides, and run the lane:

   ```sh
   python3 scripts/make-challenge.py --brief <Brief>
   lake build Challenge<Brief> Solution<Brief>
   scripts/comparator.sh <Brief>
   ```

4. Run a negative control (below), and add the lane to the table above.

## What the challenge trusts

The challenge imports Mathlib, physlib and TauCeti at the commits `lake-manifest.json` pins; their
definitions are trusted as they stand. Everything this project defines (`ForMathlib`, `ForPhyslib`,
the brief libraries) is copied into the challenge instead. `scripts/make-challenge.py` runs a
metaprogram over the solution's environment that collects the compared closure: every declaration of
the project reached from a certified theorem's type, following the types and values of definitions
and the proofs of theorems, as comparator walks it. It then copies each of them from its source
file, docstrings and comments dropped, and cuts the certified theorems at their `:=` with a `sorry`
proof (a theorem stated with `where` is cut there, and the `:=` of a `letI` inside a statement is
skipped). Each copied part keeps the `namespace`, `section`, `open`, `variable`, `include`,
`omit` and notation commands of its source that some copied declaration follows. An `open` naming
project declarations that are not copied keeps only the names the copy has. The generator refuses a
theorem whose closure reaches a `private` constant, because a private name embeds its module's
name and no challenge can reproduce it.

So reading a lane's `Challenge<Brief>.lean` is enough to know what has been proved, on top of the
three libraries.

## Why the challenge looks the way it does

Comparator compares definitions by value and does not quotient by proof irrelevance, so a
challenge that only *means* the same is rejected. The flat file therefore reproduces how the
development elaborates:

- **Load order.** Lean tries instances of equal priority latest-loaded first. The challenge imports
  its external modules in the order the development loads them, and drops an import only when an
  earlier one already loads it and makes it visible. Where the development's modules disagree on
  such a tie, the generator's `TIES` table restores each module's choice locally; no lane has
  needed it yet. An instance that a module never loads but the flat file does can change that
  module's choice too, by outranking it or by opening a path where the module's search fails and
  falls back. The `ABSENT` table lists such instances; the part copied from a module that does not
  load one erases it with `attribute [-instance]`, which the end of the part's section undoes. The
  ProjectiveMeasurement lane needs it for the instances of `Mathlib.Topology.GDelta.MetrizableSpace`
  (the path to `T0Space` of a Hilbert space) and of TauCeti's
  `Analysis.InnerProductSpace.ContinuousFunctionalCalculus` (the `cfc` of operators).
- **The auxiliary-proof cache is module-local.** Lean lifts some proofs inside a definition into
  `<owner>._proof_<n>` constants and caches them for the rest of the module. Each copied part opens
  with `run_cmd Lean.modifyEnv (Lean.Meta.auxLemmasExt.setState · {})`, which clears that cache as a
  module boundary does.
- **Copied proofs must elaborate to the same term.** Comparator compares the theorems of the
  closure by their proofs as well: a dependency with a `sorry` proof is rejected. A copied proof
  therefore cannot use what the copy lacks. `simp` lemmas proved by `rfl` leave no trace in the
  proof term, so they are never copied; and `abel`, or `simp` given an `iff` lemma, mint private
  auxiliary constants. Proofs in the closure avoid both (see `dephasingGenerator` and
  `IsTraceClass.exists_hasSum_rankOne`).

## Negative controls

On the BornRuleEntropy lane, changing `‖⟪ψ, ϕ⟫_ℂ‖ ^ 2` to `^ 3` in the challenge's `BornRule` is
rejected with `Const does not match between challenge and target 'BornRuleEntropy.BornRule'`.

On the ClassicalUncertaintyPrinciple lane, changing `hbar h` from `h / (2 * π)` to `h / π` is
rejected with `Const does not match between challenge and target
'ClassicalUncertaintyPrinciple.hbar'`, and dropping the hypothesis `hpos` of `entropy_uniform`
with `Challenge and solution theorem statement do not match:
'ClassicalUncertaintyPrinciple.entropy_uniform'`.

On the QuantumVectorSpaces lane, changing `-I * ħ` to `I * ħ` in `momOpN` is rejected with
`Const does not match between challenge and target 'QuantumVectorSpaces.momOpN'`, changing the
structure constant of `[Xⁱ, Pᵢ]` from `1` to `2` in `obsNConst` with `Const does not match between
challenge and target 'QuantumVectorSpaces.obsNConst'`, and dropping the hypothesis `hħ` of
`topology_schwartzN` with `Challenge and solution theorem statement do not match:
'QuantumVectorSpaces.topology_schwartzN'`.

On the SuperpositionAndLinearity lane, swapping the terms of `‖ψ 0‖ ^ 2 - ‖ψ 1‖ ^ 2` in the
challenge's `blochVector` is rejected with `Const does not match between challenge and target
'QuantumMechanics.Qubit.blochVector'`, dropping the minus sign of the phase `e^{-iφ/2}` in
`stateVector` with `Const does not match between challenge and target
'SuperpositionAndLinearity.stateVector'`, and dropping the hypothesis `hψ` of
`exists_eq_smul_stateVector` with `Challenge and solution theorem statement do not match:
'SuperpositionAndLinearity.exists_eq_smul_stateVector'`.

On the SuperpositionAndMultipleMixtures lane, dropping the inverse in `(‖ψ‖ ^ 2)⁻¹` in the
challenge's `pureState` is rejected with `Const does not match between challenge and target
'SuperpositionAndMultipleMixtures.pureState'`, dropping `c₂ ≠ 0` from `QSupPur` with `Const does
not match between challenge and target 'SuperpositionAndMultipleMixtures.QSupPur'`, and dropping
the hypothesis `hϕ` of `qSupPur_iff_qSupMix` with `Challenge and solution theorem statement do
not match: 'SuperpositionAndMultipleMixtures.qSupPur_iff_qSupMix'`.

On the InconsistentConvergence lane, changing the amplitude `√(1 / j)` to `√(2 / j)` in the
challenge's `ampⱼ` is rejected with `Const does not match between challenge and target
'InconsistentConvergence.ampⱼ'`, dropping the square of `‖x n‖ ^ 2` in `numberExp` with `Const
does not match between challenge and target 'InconsistentConvergence.numberExp'`, and dropping the
hypothesis `hj` of `numberExp_e` with `Challenge and solution theorem statement do not match:
'InconsistentConvergence.numberExp_e'`.

On the ProjectiveMeasurement lane, changing `f a < f b` to `f a ≤ f b` in the challenge's
`IsUniqueMinOn` is rejected with `Const does not match between challenge and target
'ProjectiveMeasurement.IsUniqueMinOn'`, swapping the arguments of `relEntropy ρ σ` in `EqKL` with
`Const does not match between challenge and target 'ProjectiveMeasurement.EqKL'`, and dropping the
hypothesis `hS` of `InfiniteDimensional.relativeEntropy_pinching_eq` with `Challenge and solution
theorem statement do not match:
'ProjectiveMeasurement.InfiniteDimensional.relativeEntropy_pinching_eq'`.

Re-run a control after any change to the generator.
