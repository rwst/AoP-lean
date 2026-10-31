/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Separable Hilbert spaces are `ℓ²(ℕ)`

Mathlib has Hilbert bases (`HilbertBasis`) and their existence (`exists_hilbertBasis`), but
not the classification of separable Hilbert spaces. This file proves that every separable,
infinite-dimensional Hilbert space has a Hilbert basis indexed by `ℕ`, and is therefore
isometrically isomorphic to `ℓ²(ℕ)`.

## Main results

* `Orthonormal.countable`: an orthonormal family in a separable space is countable;
* `HilbertBasis.finiteDimensional`: a Hilbert basis with a finite index set spans a
  finite-dimensional space;
* `nonempty_hilbertBasis_nat`, `nonempty_linearIsometryEquiv_lp_nat`: the classification.
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An orthonormal family in a separable space is countable: its members are `√2` apart. -/
theorem Orthonormal.countable [TopologicalSpace.SeparableSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2))
    (fun i j hij => Metric.ball_disjoint_ball ?_) (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  have h2 : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq 𝕜, hv.1 i, hv.1 j, hv.2 hij]
    simp
    norm_num
  nlinarith [dist_nonneg (x := v i) (y := v j)]

/-- A Hilbert basis indexed by a finite type spans a finite-dimensional space. -/
theorem HilbertBasis.finiteDimensional {ι : Type*} [Finite ι] (b : HilbertBasis ι 𝕜 E) :
    FiniteDimensional 𝕜 E := by
  set S := Submodule.span 𝕜 (Set.range b)
  have : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range b)
  have hS : S = ⊤ := by
    rw [← b.dense_span, (Submodule.closed_of_finiteDimensional S).submodule_topologicalClosure_eq]
  have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := hS ▸ inferInstance
  exact Submodule.topEquiv.finiteDimensional

/-- A separable infinite-dimensional Hilbert space has a Hilbert basis indexed by `ℕ`. -/
theorem nonempty_hilbertBasis_nat [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (hinf : ¬ FiniteDimensional 𝕜 E) : Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Countable w := b.orthonormal.countable
  have : Infinite w := by
    by_contra h
    have : Finite w := not_infinite_iff_finite.mp h
    exact hinf b.finiteDimensional
  have := Encodable.ofCountable w
  let := Denumerable.ofEncodableOfInfinite w
  let e : ℕ ≃ w := (Denumerable.eqv w).symm
  refine ⟨HilbertBasis.mk (v := b ∘ e) (b.orthonormal.comp e e.injective) ?_⟩
  rw [Set.range_comp, e.range_eq_univ, Set.image_univ, b.dense_span]

/-- A separable infinite-dimensional Hilbert space is isometrically isomorphic to `ℓ²(ℕ)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (hinf : ¬ FiniteDimensional 𝕜 E) :
    Nonempty (E ≃ₗᵢ[𝕜] lp (fun _ : ℕ => 𝕜) 2) :=
  (nonempty_hilbertBasis_nat hinf).map HilbertBasis.repr

/-- Any two separable infinite-dimensional Hilbert spaces are isometrically isomorphic. -/
theorem nonempty_linearIsometryEquiv_of_separable {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [CompleteSpace F] [TopologicalSpace.SeparableSpace F] (hE : ¬ FiniteDimensional 𝕜 E)
    (hF : ¬ FiniteDimensional 𝕜 F) : Nonempty (E ≃ₗᵢ[𝕜] F) := by
  obtain ⟨e₁⟩ := nonempty_linearIsometryEquiv_lp_nat hE
  obtain ⟨e₂⟩ := nonempty_linearIsometryEquiv_lp_nat hF
  exact ⟨e₁.trans e₂.symm⟩
