/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# The Hopf map is a submersion

The **Hopf map** sends a unit vector `v` of `ℂⁿ⁺¹ = EuclideanSpace ℂ (Fin (n + 1))` to the complex
line `[v]` it spans, a point of complex projective space `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`. Its source
is the unit sphere `S²ⁿ⁺¹`, a real manifold modelled on `EuclideanSpace ℝ (Fin (2 * n + 1))`; its
target carries the real structure of the standard affine atlas, modelled on `Fin n → ℂ`.

Near a point `p` with `p i ≠ 0`, the Hopf map read in the affine chart at `i` is
`q ↦ (q (i.succAbove j) / q i)ⱼ`, hence smooth. It has the smooth local section
`y ↦ s / ‖s‖` with `s = p i • Fin.insertNth i 1 (affineChart i y)`, which sends `[p]` back to `p`.
So its derivative at `p` has a right inverse and is surjective, and the Hopf map is a submersion
(`Projectivization.isSubmersion_hopfMap`).

## Main results

* `Projectivization.hopfMap`: the Hopf map `S²ⁿ⁺¹ → ℂPⁿ`.
* `Projectivization.hopfMap_surjective`: every complex line contains a unit vector.
* `Projectivization.contMDiff_hopfMap`: the Hopf map is smooth.
* `Projectivization.surjective_mfderiv_hopfMap`: its derivative is surjective everywhere.
* `Projectivization.isSubmersion_hopfMap`: the Hopf map is a smooth submersion.

## References

* H. Hopf, *Über die Abbildungen der dreidimensionalen Sphäre auf die Kugelfläche*,
  Math. Ann. 104 (1931), 637–665.
-/

public section

noncomputable section

open Function Manifold Metric Module Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {n : ℕ}

/-- The unit sphere of `ℂⁿ⁺¹` has real dimension `2 * n + 1`. -/
instance fact_finrank_real_euclideanSpace_complex (n : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * n + 1 + 1) :=
  ⟨by rw [finrank_real_of_complex, finrank_euclideanSpace_fin]; ring⟩

/-- A unit vector of `ℂⁿ⁺¹` has nonzero homogeneous coordinates. -/
theorem ofLp_ne_zero_of_mem_sphere (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    (p : EuclideanSpace ℂ (Fin (n + 1))).ofLp ≠ 0 := by
  intro h
  exact ne_zero_of_mem_unit_sphere p (by simpa using congrArg (WithLp.toLp 2) h)

variable (n) in
/-- The **Hopf map** `S²ⁿ⁺¹ → ℂPⁿ`, sending a unit vector to the complex line it spans. -/
@[expose] def hopfMap (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) : ℙ ℂ (Fin (n + 1) → ℂ) :=
  mk ℂ (p : EuclideanSpace ℂ (Fin (n + 1))).ofLp (ofLp_ne_zero_of_mem_sphere p)

theorem hopfMap_apply (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    hopfMap n p = mk ℂ (p : EuclideanSpace ℂ (Fin (n + 1))).ofLp (ofLp_ne_zero_of_mem_sphere p) :=
  rfl

/-- Every complex line through the origin contains a unit vector. -/
theorem hopfMap_surjective : Surjective (hopfMap n) := by
  intro x
  induction x using ind with | h v hv =>
  set w : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 v
  have hw : w ≠ 0 := fun h ↦ hv (by simpa [w] using congrArg WithLp.ofLp h)
  refine ⟨⟨‖w‖⁻¹ • w, by simp [norm_smul, hw]⟩, ?_⟩
  rw [hopfMap_apply, mk_eq_mk_iff' ℂ _ _ _ hv]
  refine ⟨((‖w‖⁻¹ : ℝ) : ℂ), ?_⟩
  ext j
  simp [w, Complex.real_smul]

/-- The Hopf map read in the affine chart at `i`, extended to all of `ℂⁿ⁺¹`: the ratios of the
other coordinates to the `i`-th one. -/
theorem contDiffAt_ratios (i : Fin (n + 1)) {r : ℕ∞ω} {w : EuclideanSpace ℂ (Fin (n + 1))}
    (hw : w.ofLp i ≠ 0) :
    ContDiffAt ℝ r (fun w : EuclideanSpace ℂ (Fin (n + 1)) ↦
      fun j ↦ w.ofLp (i.succAbove j) / w.ofLp i) w := by
  have hc (k : Fin (n + 1)) : ContDiffAt ℝ r (fun w : EuclideanSpace ℂ (Fin (n + 1)) ↦
      w.ofLp k) w :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) ↦ ℂ) k).contDiff).contDiffAt
  refine contDiffAt_pi.2 fun j ↦ ?_
  simp_rw [div_eq_mul_inv]
  exact (hc _).mul ((hc i).inv hw)

/-- Near a point `p` with `p i ≠ 0`, the Hopf map is the inverse of the affine chart at `i` applied
to the ratios of the coordinates to the `i`-th one. -/
theorem hopfMap_eventuallyEq (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    {i : Fin (n + 1)} (hp : (p : EuclideanSpace ℂ (Fin (n + 1))).ofLp i ≠ 0) :
    hopfMap n =ᶠ[nhds p] fun q ↦ (affineChart i).symm
      (fun j ↦ (q : EuclideanSpace ℂ (Fin (n + 1))).ofLp (i.succAbove j) /
        (q : EuclideanSpace ℂ (Fin (n + 1))).ofLp i) := by
  have ho : IsOpen {q : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 |
      (q : EuclideanSpace ℂ (Fin (n + 1))).ofLp i ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  filter_upwards [ho.mem_nhds hp] with q hq
  have hmem : hopfMap n q ∈ affineOpen i := by rwa [hopfMap_apply, mk_mem_affineOpen_iff]
  have h := ((affineChart i).left_inv (by simpa using hmem)).symm
  rw [hopfMap_apply] at h ⊢
  rwa [affineChart_mk] at h

/-- The inverse of an affine chart is smooth for the real structure of projective space. -/
theorem contMDiff_affineChart_symm_real (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) r (affineChart (K := ℂ) i).symm := by
  rw [← contMDiffOn_univ]
  simpa using contMDiffOn_symm_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℂ)) (r := r) i)

/-- An affine chart is smooth on its domain for the real structure of projective space. -/
theorem contMDiffOn_affineChart_real (i : Fin (n + 1)) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) r (affineChart (K := ℂ) i) (affineOpen i) := by
  simpa using contMDiffOn_of_mem_maximalAtlas
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℂ)) (r := r) i)

/-- **The Hopf map is smooth.** -/
theorem contMDiff_hopfMap (r : ℕ∞ω) :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r (hopfMap n) := by
  intro p
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (ofLp_ne_zero_of_mem_sphere p)
  have hG : ContMDiffAt (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r
      (fun q : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦
        fun j ↦ (q : EuclideanSpace ℂ (Fin (n + 1))).ofLp (i.succAbove j) /
          (q : EuclideanSpace ℂ (Fin (n + 1))).ofLp i) p :=
    (contDiffAt_ratios i hi).contMDiffAt.comp p contMDiff_coe_sphere.contMDiffAt
  exact ((contMDiff_affineChart_symm_real i r _).comp p hG).congr_of_eventuallyEq
    (hopfMap_eventuallyEq p hi)

/-- **The derivative of the Hopf map is surjective.** Near `[p]`, with `p i ≠ 0`, the Hopf map has
the smooth section `y ↦ s / ‖s‖`, `s = p i • Fin.insertNth i 1 (affineChart i y)`, which sends
`[p]` to `p`. -/
theorem surjective_mfderiv_hopfMap (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    Surjective (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) p) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (ofLp_ne_zero_of_mem_sphere p)
  set c := (p : EuclideanSpace ℂ (Fin (n + 1))).ofLp i
  let s : (Fin n → ℂ) → EuclideanSpace ℂ (Fin (n + 1)) :=
    fun z ↦ WithLp.toLp 2 (c • Fin.insertNth (α := fun _ ↦ ℂ) i 1 z)
  have hs (z) : s z ≠ 0 := fun h ↦ smul_ne_zero hi (Fin.insertNth_one_ne_zero i z)
    (by simpa [s] using congrArg WithLp.ofLp h)
  have hsd : ContDiff ℝ ∞ s :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℂ)).symm.contDiff.comp
      (((contDiff_const (c := (1 : ℂ))).finInsertNth (F := fun _ ↦ ℂ) i contDiff_id).const_smul c)
  let σ₀ : (Fin n → ℂ) → EuclideanSpace ℂ (Fin (n + 1)) := fun z ↦ ‖s z‖⁻¹ • s z
  have hσ₀ (z) : σ₀ z ∈ sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := by
    simp [σ₀, norm_smul, hs z]
  have hσd : ContMDiff 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) ∞ (codRestrict σ₀ _ hσ₀) := by
    refine ContMDiff.codRestrict_sphere (contDiff_iff_contDiffAt.2 fun z ↦ ?_).contMDiff hσ₀
    exact (((contDiffAt_norm ℂ (hs z)).comp z hsd.contDiffAt).inv
      (norm_ne_zero_iff.2 (hs z))).smul hsd.contDiffAt
  let τ := codRestrict σ₀ _ hσ₀ ∘ affineChart (K := ℂ) i
  have hτp : τ (hopfMap n p) = p := by
    have hsp : s (affineChart i (hopfMap n p)) = p := by
      rw [hopfMap_apply, affineChart_mk]
      ext j
      simp only [s, Fin.insertNth_one_div_eq_inv_smul i _ hi, c]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_inv_cancel_left₀ hi _
    ext1
    simp [τ, σ₀, hsp]
  have hsec : hopfMap n ∘ τ =ᶠ[nhds (hopfMap n p)] id := by
    have hmem : hopfMap n p ∈ affineOpen i := by rwa [hopfMap_apply, mk_mem_affineOpen_iff]
    filter_upwards [(isOpen_affineOpen i).mem_nhds hmem] with y hy
    obtain ⟨z, rfl⟩ : ∃ z, (affineChart i).symm z = y :=
      ⟨_, (affineChart i).left_inv (by simpa using hy)⟩
    change hopfMap n (codRestrict σ₀ _ hσ₀ (affineChart i ((affineChart i).symm z))) = _
    rw [(affineChart i).right_inv (by simp), hopfMap_apply, id, affineChart_symm_apply,
      mk_eq_mk_iff' ℂ _ _ _ (Fin.insertNth_one_ne_zero i _)]
    refine ⟨((‖s z‖⁻¹ : ℝ) : ℂ) * c, ?_⟩
    ext j
    simp [σ₀, s, mul_assoc, Complex.real_smul]
  have hτ : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) τ (hopfMap n p) := by
    have hmem : hopfMap n p ∈ affineOpen i := by rwa [hopfMap_apply, mk_mem_affineOpen_iff]
    exact ((hσd _).comp _ ((contMDiffOn_affineChart_real i ∞).contMDiffAt
      ((isOpen_affineOpen i).mem_nhds hmem))).mdifferentiableAt (by simp)
  intro v
  refine ⟨mfderiv 𝓘(ℝ, Fin n → ℂ) (𝓡 (2 * n + 1)) τ (hopfMap n p) v, ?_⟩
  have h := mfderiv_comp_apply_of_eq (hopfMap n p)
    ((contMDiff_hopfMap ∞ p).mdifferentiableAt (by simp)) hτ hτp v
  rw [hsec.mfderiv_eq, mfderiv_id] at h
  exact h.symm

/-- **The Hopf map is a submersion.** -/
theorem isSubmersion_hopfMap {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSubmersion (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) r (hopfMap n) :=
  ((contMDiff_hopfMap r).isSubmersionOfComplement_of_surjective_mfderiv hr
    surjective_mfderiv_hopfMap).isSubmersion

end Projectivization
