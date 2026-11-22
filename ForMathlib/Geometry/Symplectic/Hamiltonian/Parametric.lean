/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.DifferentialForm.ParametricPrimitive

/-!
# A jointly smooth Hamiltonian for a time-dependent vector field

Let `X t` be a jointly smooth time-dependent vector field on a preconnected manifold `M` with a
two-form `σ`, and suppose that each `X t` is the Hamiltonian vector field of some function `H t`,
chosen separately for each `t`. Then the Hamiltonians can be chosen jointly smooth in `(t, x)`,
normalized by `H t x₀ = 0` at a base point.

The contractions `ι_{X_t} σ` are the slices of the one-form `B = ι_Y (pr₁^* σ)` on `M × ℝ`, where
`Y (x, t) = (X t x, 0)` is the vertical field of `X`. This form is smooth, and its slices are
exact by hypothesis, so TauCeti's smooth selection of primitives
(`TauCeti.exists_contMDiff_mvfderiv_eq_of_forall_exists`) gives a smooth function on `M × ℝ` whose
slices are primitives.

## Main results

* `TauCeti.SmoothTwoForm.exists_contMDiff_isHamiltonianVectorField`: a jointly smooth
  time-dependent vector field that is Hamiltonian at each time has a jointly smooth Hamiltonian.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace TauCeti.SmoothTwoForm

/-- **A jointly smooth Hamiltonian.** On a preconnected manifold, let `X` be a jointly smooth
time-dependent vector field such that each `X t` is the Hamiltonian vector field of a
differentiable function. Then there is one function `H (t, x)`, jointly smooth, with `H t x₀ = 0`,
such that each `X t` is the Hamiltonian vector field of `H t`. -/
theorem exists_contMDiff_isHamiltonianVectorField [PreconnectedSpace M]
    {σ : SmoothTwoForm I M} {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hH : ∀ t, ∃ f : M → ℝ, MDifferentiable I 𝓘(ℝ) f ∧ σ.IsHamiltonianVectorField f (X t))
    (x₀ : M) :
    ∃ H : ℝ → M → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ (fun p : ℝ × M ↦ H p.1 p.2) ∧
      (∀ t, H t x₀ = 0) ∧ ∀ t, σ.IsHamiltonianVectorField (H t) (X t) := by
  -- The vertical field `(x, t) ↦ (X t x, 0)` on `M × ℝ`.
  let Y : (p : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) p := fun p ↦ (X p.2 p.1, (0 : ℝ))
  have hY : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (fun p ↦ (⟨p, Y p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    have h0 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
        (fun s : ℝ ↦ (⟨s, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
    exact (contMDiff_equivTangentBundleProd_symm (I := I) (M := M) (I' := 𝓘(ℝ, ℝ))
      (M' := ℝ)).comp ((hX.comp (contMDiff_snd.prodMk contMDiff_fst)).prodMk
        (h0.comp contMDiff_snd))
  -- The one-form `B = ι_Y (pr₁^* σ)` on `M × ℝ`, whose slices are the contractions `ι_{X_t} σ`.
  let σ' : SmoothForm (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) ℝ 2 :=
    SmoothForm.mpullback Prod.fst contMDiff_fst σ
  let B : RoughForm (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) ℝ 1 := RoughForm.interior Y σ'.val
  have hB : IsSmoothForm (I.prod 𝓘(ℝ, ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    σ'.isSmoothForm.interior hY
  have hBapply (x : M) (t : ℝ) (v : E) :
      B (x, t) ![(v, (0 : ℝ))] = SmoothBundleForm.eval₂ σ x (X t x) v := by
    refine Eq.trans ?_ (SmoothBundleForm.eval₂_apply σ x (X t x) v).symm
    rw [RoughForm.interior_apply, SmoothForm.mpullback_apply, mfderiv_fst]
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨F, hF, hF0, hFd⟩ := exists_contMDiff_mvfderiv_eq_of_forall_exists hB
    (fun t ↦ by
      obtain ⟨f, hf, hfX⟩ := hH t
      exact ⟨f, hf, fun x v ↦ ((isHamiltonianVectorField_iff.1 hfX) x v).symm.trans
        (hBapply x t v).symm⟩) x₀
  exact ⟨fun t x ↦ F (x, t), hF.comp (contMDiff_snd.prodMk contMDiff_fst), hF0,
    fun t ↦ isHamiltonianVectorField_iff.2 fun x v ↦ (hBapply x t v).symm.trans
      (hFd t x v).symm⟩

end TauCeti.SmoothTwoForm
