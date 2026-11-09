/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Countable orthonormal families in infinite dimension

An infinite-dimensional inner product space has a linearly independent sequence, the vectors of a
basis along an embedding of `ℕ` into its infinite index set; the Gram–Schmidt process makes it
orthonormal. So every countable index type carries an orthonormal family.

## Main results

* `exists_orthonormal_of_not_finiteDimensional`: in infinite dimension, every countable `ι` has an
  orthonormal family `ι → E`.
-/

public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem exists_orthonormal_of_not_finiteDimensional {ι : Type*} [Countable ι]
    (h : ¬ FiniteDimensional 𝕜 E) : ∃ v : ι → E, Orthonormal 𝕜 v := by
  set b := Module.Basis.ofVectorSpace 𝕜 E
  have : Infinite (Module.Basis.ofVectorSpaceIndex 𝕜 E) := by
    rw [← not_finite_iff_infinite]
    exact fun _ => h (Module.Finite.of_basis b)
  set f : ℕ → E := b ∘ Infinite.natEmbedding _
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat ι
  exact ⟨InnerProductSpace.gramSchmidtNormed 𝕜 f ∘ g,
    (InnerProductSpace.gramSchmidtNormed_orthonormal
      (b.linearIndependent.comp _ (Infinite.natEmbedding _).injective)).comp g hg⟩
