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
| The Born rule is equivalent to the von Neumann entropy | Theorem 9 | `BornRuleEntropy.two_conditions_imply_third` | 142 lines, 7 KiB |
| Classical uncertainty principle | Corollary 1, Theorem 2 (eqs. 3 and 5), the final remark | 7 theorems, see `theorems.txt` | 101 lines, 5 KiB |
| Physical vector spaces for quantum mechanics | Corollary 2, Example 3 (in `n` dimensions) and its Remark, Example 4, Theorem 5 ([B]COBS) | 6 theorems, see `theorems.txt` | 163 lines, 7 KiB |
| Directional vectors vs quantum state vectors | eqs. (1)–(3), linearity in terms of probability, half a turn, states as rays, the outcomes as opposite directions, completeness of the forms (1) and (3) | 13 theorems, see `theorems.txt` | 83 lines, 4 KiB |
| Superpositions correspond to multiple decompositions | Theorem 1 and its two directions (eqs. 3 and 4), eq. (2), the support argument, mixtures of independent states are not pure | 6 theorems, see `theorems.txt` | 73 lines, 4 KiB |
| Inconsistent convergence in Hilbert space | eqs. (2)–(5), the convergence of `eʲ` in `ℓ²`, the eigenstates `\|j⟩` alone have no limit | 7 theorems, see `theorems.txt` | 51 lines, 2 KiB |
| Unphysicality of Hilbert spaces for quantum mechanics | Propositions 1–4 (an unbounded map is not continuous, Hellinger–Toeplitz, `N` self-adjoint and unbounded with `E_N` discontinuous at `\|0⟩`, the frame change onto `ℝ` and its density identity, both packets normalized, `L²(ℝⁿ⁺¹) ≅ L²(ℝᵐ⁺¹)`), Theorem 5 ([B]COBS, [B]WDQ, [B]STDIST in their minimum forms) | 11 theorems, see `theorems.txt` | 474 lines, 24 KiB |
| Projective measurements are equilibration processes | Theorem 1 (EQ-LIND, EQ-HS, EQ-KL ⇔ EQ-MEAS, eqs. 2–12) and eq. (13), in finite dimension and in any dimension | 10 theorems, see `theorems.txt` | 704 lines, 37 KiB |
| Multiple equivalent characterizations of the Schrödinger equation | Proposition 1, also for maps preserving only equal mixtures, and the remark after it (injective suffices in finite dimension), Theorem 3 with each of its implications, in finite dimension and in any dimension, and in finite dimension as the brief states it (two-parameter evolution, DR-SCEQ with H(t)) | 25 theorems, see `theorems.txt` | 454 lines, 24 KiB |
| Equivalence of sup-norm, L¹, and L² seminorms on the Schwartz space | Steps 1–3 (eqs. 6, 7 and 9, with the hypothesis eq. 9 needs), Theorem 5 (the finiteness conditions, the space (4) and its sup seminorms as Mathlib's, the three seminorm families generate one topology), eq. (10) | 12 theorems, see `theorems.txt` | 269 lines, 14 KiB |
| Non-uniqueness of the moment problem for Schwartz functions | eq. (3), the states `ψ_θ` as distinct rays, the bumps of Fig. 1, Theorem 1 | 6 theorems, see `theorems.txt` | 58 lines, 3 KiB |
| Non-linear representations in quantum mechanics | eq. (2), Proposition 1, Corollary 3, the mathematical steps of the proof of Theorem 4 (Born rule as cos² of the Fubini–Study distance, `m(H)` with the same rays and Born rule, the moved-over `\|v⟩⟨v\|` not additive), the Conclusion's `m` not preserving the inner product | 11 theorems, see `theorems.txt` | 179 lines, 9 KiB |
| Schrödinger equation is equivalent to information conservation | Corollary 1 (the entropy of the equal mixture, strictly decreasing in `p`, the iff), Theorem 2 in both directions, in finite dimension, at every time for a two-parameter evolution, in any dimension, and with an unbounded `H` for a time-independent evolution | 11 theorems, see `theorems.txt` | 357 lines, 19 KiB |

Lanes are meant for the briefs whose `open-problems.tex` has no item marked
`[blocks verification]`: BornRuleEntropy, ClassicalUncertaintyPrinciple, EntropyTopology,
HilbertUnphysicality, InconsistentConvergence, NonLinearQuantum, ProjectiveMeasurement,
QuantumVectorSpaces, SchroedingerEvolution, SchwartzMomentProblem, SchwartzNorms,
SuperpositionAndLinearity, SuperpositionAndMultipleMixtures and UnitaryEntropy.

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
and the proofs of theorems, as comparator walks it. To these it adds the project's instances whose
types name only collected declarations, with their own closures: elaboration uses them without
leaving a trace in the terms (a `CoeFun` is unfolded on the spot). It then copies each of them from
its source file, docstrings and comments dropped, and cuts the certified theorems at their `:=` with
a `sorry` proof (a theorem stated with `where` is cut there, and the `:=` of a `letI` inside a
statement is skipped). Each copied part keeps the `namespace`, `section`, `open`, `variable`,
`include`, `omit` and notation commands of its source that some copied declaration follows. An
`open` naming project declarations that are not copied keeps only the names the copy has. The
generator refuses a theorem whose closure reaches a `private` constant, because a private name
embeds its module's name and no challenge can reproduce it.

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
  needed it yet. An instance that a module never sees but the flat file does can change that
  module's choice too, by outranking it or by opening a path where the module's search fails and
  falls back. (A file sees the modules it imports and what they import publicly, recursively; a
  module loaded only through a private import stays hidden.) The `ABSENT` table lists such
  instances; the part copied from a module that does not see one erases it with
  `attribute [-instance]`, which the end of the part's section undoes, and only where the flat
  file sees it. The
  ProjectiveMeasurement lane needs it for the instances of `Mathlib.Topology.GDelta.MetrizableSpace`
  (the path to `T0Space` of a Hilbert space) and of TauCeti's
  `Analysis.InnerProductSpace.ContinuousFunctionalCalculus` (the `cfc` of operators), the
  SchroedingerEvolution lane for `instCommCStarAlgebraComplex` (the path to `NormedCommRing ℂ`).
  Erasing every instance a module does not see would be exact, but adds hundreds of lines to
  each part, so the table lists only those comparator has rejected.
- **The auxiliary-proof cache is module-local.** Lean lifts some proofs inside a definition into
  `<owner>._proof_<n>` constants and caches them for the rest of the module. Each copied part opens
  with `run_cmd Lean.modifyEnv (Lean.Meta.auxLemmasExt.setState · {})`, which clears that cache as a
  module boundary does.
- **Copied proofs must elaborate to the same term.** Comparator compares the theorems of the
  closure by their proofs as well: a dependency with a `sorry` proof is rejected. A copied proof
  therefore cannot use what the copy lacks. `simp` lemmas proved by `rfl` leave no trace in the
  proof term, so they are never copied. `abel`, `decide +kernel` (which closes the index side goals
  of `List.TFAE.out`), and `simp` given an `iff` lemma or a reversed one (`← h`) mint private
  auxiliary constants. Proofs in the closure avoid them (see `dephasingGenerator`,
  `IsTraceClass.exists_hasSum_rankOne`, `NonLinearQuantum.nlMap_neg_nlMap`, which rewrites with
  `← Complex.exp_add` instead of simplifying with it, and `SchwartzNorms.l2Norm_lt_top`, which
  passes the side goals explicitly).

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

On the SchroedingerEvolution lane, changing `(I * ħ)⁻¹` to `I * ħ` in the challenge's `DrSceq` is
rejected with `Const does not match between challenge and target 'SchroedingerEvolution.DrSceq'`,
dropping the surjectivity from `InfiniteDimensional.DrInfo` with `Const does not match between
challenge and target 'SchroedingerEvolution.InfiniteDimensional.DrInfo'`, and dropping the
hypothesis `hħ` of `drUnit_iff_drSceq` with `Challenge and solution theorem statement do not
match: 'SchroedingerEvolution.drUnit_iff_drSceq'`. Dropping the injectivity `hinj` from
`bijOnPure_of_injOn` is rejected with `Challenge and solution theorem statement do not match:
'SchroedingerEvolution.bijOnPure_of_injOn'`. Changing `Φ (t₁ - t₀)` to `Φ (t₁ + t₀)` in
`TwoParameter.Evti` is rejected with `Const does not match between challenge and target
'SchroedingerEvolution.TwoParameter.Evti'`, replacing the propagator `U t₁ U t₀†` of
`TwoParameter.DrSceq` by `U t₀† U t₁` with `Const does not match between challenge and target
'SchroedingerEvolution.TwoParameter.DrSceq'`, and dropping `hħ` from `TwoParameter.drSceq_iff`
with `Challenge and solution theorem statement do not match:
'SchroedingerEvolution.TwoParameter.drSceq_iff'`. Dropping `hmix` from
`affine_pure_state_correspondence_of_map_mix` is rejected with `Challenge and solution theorem
statement do not match: 'SchroedingerEvolution.affine_pure_state_correspondence_of_map_mix'`,
changing the weights of `mix` from `2⁻¹` to `3⁻¹` with `Const does not match between challenge
and target 'QuantumMechanics.Wigner.mix'`, and dropping `hD` from
`InfiniteDimensional.affine_pure_state_correspondence_of_map_mix` with `Challenge and solution
theorem statement do not match:
'SchroedingerEvolution.InfiniteDimensional.affine_pure_state_correspondence_of_map_mix'`.

On the SchwartzNorms lane, swapping `α` and `β` in the challenge's `supNorm` is rejected with
`Const does not match between challenge and target 'SchwartzNorms.supNorm'`, dropping the
hypothesis `h` of `supNorm_le` with `Challenge and solution theorem statement do not match:
'SchwartzNorms.supNorm_le'`, and replacing `√(π / 2)` by `√(π / 4)` in `l1Norm_le` with the same
message for `'SchwartzNorms.l1Norm_le'`. Each control ran with a configuration naming only the
theorem it touches.

On the SchwartzMomentProblem lane, changing `-I * ħ` to `I * ħ` in the challenge's `density` is
rejected with `Const does not match between challenge and target
'SchwartzMomentProblem.density'`, dropping the hypothesis `hfg` of `moment_psi` with `Challenge
and solution theorem statement do not match: 'SchwartzMomentProblem.moment_psi'`, and changing the
inner radius of `realBump` from `1 / 2` to `1 / 3` with `Const does not match between challenge
and target 'SchwartzMomentProblem.realBump'`. Each control ran with a configuration naming only
the theorem it touches.

On the NonLinearQuantum lane, changing `‖x‖ * ‖y‖` to `‖x‖ + ‖y‖` in the challenge's `fsDist` is
rejected with `Const does not match between challenge and target 'NonLinearQuantum.fsDist'`,
turning `swapOp` into the identity `⟨v, x⟩ v + ⟨w, x⟩ w` (still self-adjoint and unitary) with
`Const does not match between challenge and target 'NonLinearQuantum.swapOp'`, changing the
projector `x ↦ ⟨v, x⟩ v` of `projOp` to `x ↦ ⟨v, x⟩ (2 • v)` with `Const does not match between
challenge and target 'NonLinearQuantum.projOp'`, and dropping the hypothesis `hE` of
`swapOp_mem_unitary` with `Challenge and solution theorem statement do not match:
'NonLinearQuantum.swapOp_mem_unitary'`. Each control ran with a configuration naming only the
theorem it touches.

On the UnitaryEntropy lane, changing `‖⟪ψ, ϕ⟫_ℂ‖ ^ 2` to `^ 3` in the challenge's `born` is
rejected with `Const does not match between challenge and target 'UnitaryEntropy.born'`, changing
`r < t` to `r ≤ t` in `TwoParameter.EvDiff` (differentiability also at the reference time) with
`Const does not match between challenge and target 'UnitaryEntropy.TwoParameter.EvDiff'`, and
dropping the hypothesis `hħ` of the unbounded `drSceq_iff_drInfo_and_evDiff` with `Challenge and
solution theorem statement do not match: 'UnitaryEntropy.drSceq_iff_drInfo_and_evDiff'`. Each
control ran with a configuration naming only the theorem it touches.

On the HilbertUnphysicality lane, changing `x ψ` to `x² ψ` in the challenge's `positionDomain` is
rejected with `Const does not match between challenge and target
'HilbertUnphysicality.positionDomain'`, changing the entries of `numberOp` from `n` to `n + 1`
with `Const does not match between challenge and target 'HilbertUnphysicality.numberOp'`, and
weakening `D(N) ∖ {0}` to `D(N)` in `theorem5` with `Challenge and solution theorem statement do
not match: 'HilbertUnphysicality.theorem5'`. Each control ran with a configuration naming
`theorem5` and the certified theorems in its closure, `surjective_frameChange` (through
`frameIso`) and `integral_gaussDensity` (through `gaussState`): a certified theorem has a `sorry`
proof in the challenge, so a configuration that omits it while keeping a theorem whose closure
reaches it is rejected with `Const does not match` for that theorem, whatever the change.

Re-run a control after any change to the generator.
