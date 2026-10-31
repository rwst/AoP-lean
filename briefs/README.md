<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-->

# Formalized briefs

The [technical briefs](https://assumptionsofphysics.org/resources/briefs) of the Assumptions of
Physics project, one directory each.

- [SuperpositionAndLinearity](SuperpositionAndLinearity/) — Directional vectors vs quantum state
  vectors
- [SuperpositionAndMultipleMixtures](SuperpositionAndMultipleMixtures/) — Superpositions
  correspond to multiple decompositions
- [BornRuleEntropy](BornRuleEntropy/) — The Born rule is equivalent to the von Neumann entropy
- [ClassicalUncertaintyPrinciple](ClassicalUncertaintyPrinciple/) — Classical uncertainty
  principle
- [PureStatesNotEnough](PureStatesNotEnough/) — Quantum pure states are not enough
- [InconsistentConvergence](InconsistentConvergence/) — Inconsistent convergence in Hilbert space
- [SchwartzMomentProblem](SchwartzMomentProblem/) — Non-uniqueness of the moment problem for
  Schwartz functions
- [NonLinearQuantum](NonLinearQuantum/) — Non-linear representations in quantum mechanics
- [UnitaryEntropy](UnitaryEntropy/) — Schrödinger equation is equivalent to information
  conservation
- [SchwartzNorms](SchwartzNorms/) — Equivalence of sup-norm, L¹, and L² seminorms on the Schwartz
  space
- [EntropyTopology](EntropyTopology/) — Entropy is not continuous in standard probability spaces
- [SchroedingerEvolution](SchroedingerEvolution/) — Multiple equivalent characterizations of the
  Schrödinger equation
- [HilbertUnphysicality](HilbertUnphysicality/) — Unphysicality of Hilbert spaces for quantum
  mechanics
- [QuantumVectorSpaces](QuantumVectorSpaces/) — Physical vector spaces for quantum mechanics
- [ProjectiveMeasurement](ProjectiveMeasurement/) — Projective measurements are equilibration
  processes
- [UnitaryProjectiveEvolution](UnitaryProjectiveEvolution/) — Unitary evolution as infinitesimal
  projective processes

## What a directory contains

- `<Brief>.pdf` — the brief itself.
- `<Brief>.lean` — the Lean formalization; a few larger ones are split into modules under
  `<Brief>/`.
- `formalization-log.tex` / `.pdf` — which statements of the brief were checked, how the Lean
  version differs, and the problems found in the brief.
- `open-problems.tex` / `.pdf` — what remains open, from the brief and from the formalization;
  items marked *blocks verification* stand in the way of checking a main claim.
- `comparator/` — where present, the certification of the main theorems with `lake comparator`:
  the generated challenge, the solution and its configuration (see
  [COMPARATOR.md](../COMPARATOR.md)).
