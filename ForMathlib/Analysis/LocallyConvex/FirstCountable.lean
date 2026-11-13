/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Countable subfamilies of seminorms in first-countable spaces

Mathlib's `WithSeminorms.firstCountableTopology` says that a topology induced by a countable
family of seminorms is first countable. This file proves the converse: if a family of seminorms
induces a first-countable topology, then a countable subfamily already induces it.

## Main results

* `WithSeminorms.exists_countable`: a family of seminorms inducing a first-countable topology has
  a countable subfamily inducing the same topology.
-/

open Filter Topology

@[expose] public section

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] {p : SeminormFamily 𝕜 E ι}

/-- If a family of seminorms induces a first-countable topology, then a countable subfamily
induces the same topology. Converse of `WithSeminorms.firstCountableTopology`. -/
theorem WithSeminorms.exists_countable [FirstCountableTopology E] (hp : WithSeminorms p) :
    ∃ s : Set ι, s.Countable ∧ WithSeminorms fun i : s => p i := by
  classical
  obtain ⟨x, hx0, hx⟩ := hp.hasBasis_zero_ball.exists_antitone_subbasis
  let s : Set ι := ⋃ n, ((x n).1 : Set ι)
  refine ⟨s, Set.countable_iUnion fun n => (x n).1.countable_toSet, ?_⟩
  have := hp.isTopologicalAddGroup
  have hsup (t : Finset s) :
      (t.sup fun i : s => p i) = (t.map (Function.Embedding.subtype _)).sup p := by
    rw [Finset.sup_map]; rfl
  refine SeminormFamily.withSeminorms_of_hasBasis _ ⟨fun U => ?_⟩
  simp only [SeminormFamily.basisSets_iff, id]
  constructor
  · intro hU
    obtain ⟨n, -, hn⟩ := hx.1.mem_iff.1 hU
    have hs : ∀ i ∈ (x n).1, i ∈ s := fun i hi => Set.mem_iUnion.2 ⟨n, hi⟩
    refine ⟨_, ⟨(x n).1.subtype (· ∈ s), (x n).2, hx0 n, rfl⟩, ?_⟩
    rwa [hsup, Finset.subtype_map_of_mem hs]
  · rintro ⟨_, ⟨t, r, hr, rfl⟩, hU⟩
    rw [hsup] at hU
    exact mem_of_superset (hp.hasBasis_zero_ball.mem_of_mem (i := (_, r)) hr) hU
