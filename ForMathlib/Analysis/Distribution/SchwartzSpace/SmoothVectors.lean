/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteOscillator
public import ForMathlib.Analysis.Distribution.SchwartzSpace.SchrodingerRep

/-!
# The Schwartz space is the space of smooth vectors of the Schrödinger representation

Let `ρ` be the Schrödinger representation of the polarized Heisenberg group on `L²(ℝ^ι)`,
`ι` finite and nonempty (`Heisenberg.schrodinger`). A vector `g ∈ L²` is *smooth* when its orbit
`p ↦ ρ(p) g` is a smooth map into `L²`. The smooth vectors are exactly the Schwartz functions.

That Schwartz functions are smooth vectors is `Heisenberg.contDiff_schrodinger_toLp`. For the
converse, let `g` be a smooth vector, and let `Δ g` be the sum over `j` of the second derivatives
of the orbit at `0` in the directions of `aⱼ` and of `bⱼ`. Pairing with a Schwartz function `h`
and moving `ρ` to `h` gives `⟪h, Δ g⟫ = ⟪∑ⱼ (∂ⱼ² - xⱼ²) h, g⟫ = ⟪-2 H h, g⟫`, with `H` the
harmonic oscillator. For the Hermite function `h_α` this is `-2 λ_α ⟪h_α, g⟫`. Since
`ρ(p) Δ g` is a second derivative of the smooth map `q ↦ ρ(pq) g`, the vector `Δ g` is again
smooth. So `λ_αᵏ ⟪h_α, g⟫` are the Hermite coefficients of `(-Δ/2)ᵏ g ∈ L²` for every `k`, and `g`
is a Schwartz function (`SchwartzMap.exists_toLp_eq_of_forall_exists_inner`).

## Main definitions

* `Heisenberg.laplacian g`: `∑ⱼ (∂²_{aⱼ} + ∂²_{bⱼ}) ρ(p) g` at `p = 0`.

## Main results

* `Heisenberg.contDiff_schrodinger_iff`: `g ∈ L²(ℝ^ι)` is a smooth vector of the Schrödinger
  representation iff it is a Schwartz function.

## References

* R. Goodman, Analytic and entire vectors for representations of Lie groups, Trans. Amer. Math.
  Soc. 143 (1969) 55–76, Sec. 6 (`ι` a singleton, from his Theorem 1.1).
* G. B. Folland, *Harmonic Analysis in Phase Space*, Princeton 1989, Ch. 1.
-/

@[expose] public noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped ContDiff InnerProductSpace LineDeriv

namespace Heisenberg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option hygiene false in
local notation "Eι" => EuclideanSpace ℝ ι

set_option hygiene false in
local notation "𝓗" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))

/-! ### Second derivatives of an orbit along a line -/

omit [DecidableEq ι] in
/-- If `⟪h, O(t v)⟫ = ⟪ψ t, g⟫` for all `t`, the second derivatives at `0` agree. -/
lemma inner_fderiv_fderiv_eq {O : Eι × Eι × ℝ → 𝓗} (hO : ContDiff ℝ 2 O) (v : Eι × Eι × ℝ)
    (h g : 𝓗) {ψ ψ₁ ψ₂ : ℝ → 𝓗} (hψ : ∀ t, HasDerivAt ψ (ψ₁ t) t)
    (hψ₁ : ∀ t, HasDerivAt ψ₁ (ψ₂ t) t) (heq : ∀ t : ℝ, ⟪h, O (t • v)⟫_ℂ = ⟪ψ t, g⟫_ℂ) :
    ⟪h, fderiv ℝ (fderiv ℝ O) 0 v v⟫_ℂ = ⟪ψ₂ 0, g⟫_ℂ := by
  have hd1 : Differentiable ℝ O := hO.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ O) :=
    (hO.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hχ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => O (s • v)) (fderiv ℝ O (t • v) v) t := fun t => by
    have := (hd1 (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
    simpa only [one_smul, Function.comp_def, id] using this
  have hχ₁ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ O (s • v) v)
      (fderiv ℝ (fderiv ℝ O) (t • v) v v) t := fun t => by
    have := (hd2 (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
    simpa only [one_smul, Function.comp_def, id, map_zero, add_zero] using
      this.clm_apply (hasDerivAt_const t v)
  -- First derivatives.
  have hF : ∀ t, HasDerivAt (fun s : ℝ => ⟪h, O (s • v)⟫_ℂ) ⟪h, fderiv ℝ O (t • v) v⟫_ℂ t :=
    fun t => by simpa using (hasDerivAt_const t h).inner ℂ (hχ t)
  have hG : ∀ t, HasDerivAt (fun s : ℝ => ⟪ψ s, g⟫_ℂ) ⟪ψ₁ t, g⟫_ℂ t :=
    fun t => by simpa using (hψ t).inner ℂ (hasDerivAt_const t g)
  have e : (fun s : ℝ => ⟪h, O (s • v)⟫_ℂ) = fun s => ⟪ψ s, g⟫_ℂ := funext heq
  have h1 : ∀ t, ⟪h, fderiv ℝ O (t • v) v⟫_ℂ = ⟪ψ₁ t, g⟫_ℂ := fun t => by
    have := hF t
    rw [e] at this
    exact this.unique (hG t)
  -- Second derivatives.
  have hF₁ : HasDerivAt (fun s : ℝ => ⟪h, fderiv ℝ O (s • v) v⟫_ℂ)
      ⟪h, fderiv ℝ (fderiv ℝ O) ((0 : ℝ) • v) v v⟫_ℂ 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) h).inner ℂ (hχ₁ 0)
  have hG₁ : HasDerivAt (fun s : ℝ => ⟪ψ₁ s, g⟫_ℂ) ⟪ψ₂ 0, g⟫_ℂ 0 := by
    simpa using (hψ₁ 0).inner ℂ (hasDerivAt_const (0 : ℝ) g)
  rw [funext h1, zero_smul] at hF₁
  exact hF₁.unique hG₁

variable (g : 𝓗)

/-- The direction `aⱼ` of the translations. -/
def dirA (j : ι) : Eι × Eι × ℝ := (EuclideanSpace.single j 1, 0, 0)

/-- The direction `bⱼ` of the modulations. -/
def dirB (j : ι) : Eι × Eι × ℝ := (0, EuclideanSpace.single j 1, 0)

/-- `Δ g = ∑ⱼ (∂²_{aⱼ} + ∂²_{bⱼ}) ρ(p) g` at `p = 0`. -/
def laplacian : 𝓗 :=
  ∑ j, (fderiv ℝ (fderiv ℝ fun p => schrodinger p g) 0 (dirA j) (dirA j) +
    fderiv ℝ (fderiv ℝ fun p => schrodinger p g) 0 (dirB j) (dirB j))

variable {g}

lemma inner_fderiv_fderiv_dirA (hg : ContDiff ℝ ∞ fun p => schrodinger p g)
    (h : 𝓢(Eι, ℂ)) (j : ι) :
    ⟪h.toLp 2, fderiv ℝ (fderiv ℝ fun p => schrodinger p g) 0 (dirA j) (dirA j)⟫_ℂ =
      ⟪(coordDerivCLM j (coordDerivCLM j h)).toLp 2, g⟫_ℂ := by
  set u : Eι := EuclideanSpace.single j 1
  have := inner_fderiv_fderiv_eq (hg.of_le (by simp)) (dirA j) (h.toLp 2) g
    (fun t => hasDerivAt_schrodinger_toLp_fst h (-u) t)
    (fun t => hasDerivAt_schrodinger_toLp_fst (∂_{-u} h) (-u) t)
    (fun t => by rw [inner_schrodinger_right, dirA, inv_smul_fst])
  rw [this, zero_smul, schrodinger_zero, coordDerivCLM_apply, coordDerivCLM_apply,
    LineDeriv.lineDerivOp_left_neg, LineDeriv.lineDerivOp_left_neg, LineDeriv.lineDerivOp_neg,
    neg_neg]

lemma inner_fderiv_fderiv_dirB (hg : ContDiff ℝ ∞ fun p => schrodinger p g)
    (h : 𝓢(Eι, ℂ)) (j : ι) :
    ⟪h.toLp 2, fderiv ℝ (fderiv ℝ fun p => schrodinger p g) 0 (dirB j) (dirB j)⟫_ℂ =
      ⟪(-coordMulCLM j (coordMulCLM j h)).toLp 2, g⟫_ℂ := by
  set w : Eι := EuclideanSpace.single j 1
  have := inner_fderiv_fderiv_eq (hg.of_le (by simp)) (dirB j) (h.toLp 2) g
    (fun t => hasDerivAt_schrodinger_toLp_snd h (-w) t)
    (fun t => hasDerivAt_schrodinger_toLp_snd (I • innerMul (-w) h) (-w) t)
    (fun t => by rw [inner_schrodinger_right, dirB, inv_smul_snd])
  rw [this, zero_smul, schrodinger_zero]
  congr 2
  ext x
  simp [w, EuclideanSpace.inner_single_left]
  ring_nf
  rw [I_sq]
  ring

/-- `⟪h, Δ g⟫ = ⟪-2 H h, g⟫` for a Schwartz function `h`. -/
lemma inner_laplacian (hg : ContDiff ℝ ∞ fun p => schrodinger p g) (h : 𝓢(Eι, ℂ)) :
    ⟪h.toLp 2, laplacian g⟫_ℂ = ⟪((-2 : ℂ) • oscillatorCLM h).toLp 2, g⟫_ℂ := by
  have hH : (-2 : ℂ) • oscillatorCLM h =
      ∑ j, (coordDerivCLM j (coordDerivCLM j h) + -coordMulCLM j (coordMulCLM j h)) := by
    simp only [oscillatorCLM, _root_.smul_apply, _root_.sum_apply, _root_.sub_apply,
      ContinuousLinearMap.comp_apply, smul_smul]
    norm_num
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hsum : ∀ s : ι → 𝓢(Eι, ℂ), (∑ j, s j).toLp 2 = ∑ j, (s j).toLp 2 :=
    fun s => map_sum (toLpCLM ℂ ℂ 2 volume) s Finset.univ
  have hadd : ∀ a b : 𝓢(Eι, ℂ), (a + b).toLp 2 volume = a.toLp 2 volume + b.toLp 2 volume :=
    fun a b => map_add (toLpCLM ℂ ℂ 2 volume) a b
  rw [laplacian, inner_sum, hH, hsum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_add_right, inner_fderiv_fderiv_dirA hg, inner_fderiv_fderiv_dirB hg, hadd,
    inner_add_left]

/-- **The Hermite coefficients of `Δ g`.** `⟪h_α, Δ g⟫ = -2 λ_α ⟪h_α, g⟫`. -/
theorem inner_hermitePiBasis_laplacian (hg : ContDiff ℝ ∞ fun p => schrodinger p g)
    (α : ι → ℕ) :
    ⟪hermitePiBasis α, laplacian g⟫_ℂ =
      (-2 * oscillatorEigenvalue ι α : ℂ) * ⟪hermitePiBasis α, g⟫_ℂ := by
  rw [← toLp_hermitePi, inner_laplacian hg, ← toLpCLM_apply (𝕜 := ℂ), map_smul, toLpCLM_apply,
    toLp_oscillatorCLM_hermitePi, smul_smul, inner_smul_left, toLp_hermitePi]
  congr 1
  simp [map_mul, conj_ofReal, map_ofNat]

/-- `ρ(p) Δ g` is the second derivative at `0` of `q ↦ ρ(p q) g`. -/
lemma schrodinger_laplacian (hg : ContDiff ℝ ∞ fun p => schrodinger p g) (p : Eι × Eι × ℝ) :
    schrodinger p (laplacian g) = ∑ j,
      (fderiv ℝ (fderiv ℝ fun q => schrodinger (mul p q) g) 0 (dirA j) (dirA j) +
        fderiv ℝ (fderiv ℝ fun q => schrodinger (mul p q) g) 0 (dirB j) (dirB j)) := by
  set R : 𝓗 →L[ℝ] 𝓗 := (schrodinger p).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  have hR : (fun q => schrodinger (mul p q) g) = R ∘ fun q => schrodinger q g :=
    funext fun q => (schrodinger_schrodinger p q g).symm
  have key : ∀ v, fderiv ℝ (fderiv ℝ fun q => schrodinger (mul p q) g) 0 v v =
      schrodinger p (fderiv ℝ (fderiv ℝ fun q => schrodinger q g) 0 v v) := by
    intro v
    have e1 := iteratedFDeriv_two_apply (𝕜 := ℝ) (fun q => schrodinger (mul p q) g) 0 ![v, v]
    have e2 := iteratedFDeriv_two_apply (𝕜 := ℝ) (fun q => schrodinger q g) 0 ![v, v]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2
    rw [← e1, ← e2, hR, R.iteratedFDeriv_comp_left hg.contDiffAt (by simp)]
    rfl
  rw [laplacian, map_sum]
  simp only [map_add, key]

omit [DecidableEq ι] in
/-- For smooth `O`, the second derivative at `0` of `q ↦ O(p q)` depends smoothly on `p`. -/
lemma contDiff_fderiv_fderiv_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {O : Eι × Eι × ℝ → V} (hO : ContDiff ℝ ∞ O) (v w : Eι × Eι × ℝ) :
    ContDiff ℝ ∞ fun p => fderiv ℝ (fderiv ℝ fun q => O (mul p q)) 0 v w := by
  have h0 : ContDiff ℝ ∞ fun y : ((Eι × Eι × ℝ) × (Eι × Eι × ℝ)) × (Eι × Eι × ℝ) =>
      O (mul y.1.1 y.2) :=
    hO.comp (contDiff_mul.comp (contDiff_fst.fst.prodMk contDiff_snd))
  have h1 : ContDiff ℝ ∞ fun x : (Eι × Eι × ℝ) × (Eι × Eι × ℝ) =>
      fderiv ℝ (fun q => O (mul x.1 q)) x.2 := by
    refine ContDiff.fderiv (m := ∞) ?_ contDiff_snd (by simp)
    rw [Function.uncurry_def]
    exact h0
  have h2 : ContDiff ℝ ∞ fun p : Eι × Eι × ℝ =>
      fderiv ℝ (fun q => fderiv ℝ (fun q' => O (mul p q')) q) 0 := by
    refine ContDiff.fderiv (m := ∞) ?_ contDiff_const (by simp)
    rw [Function.uncurry_def]
    exact h1
  exact (h2.clm_apply contDiff_const).clm_apply contDiff_const

/-- **Smooth vectors are preserved by `Δ`.** -/
theorem contDiff_schrodinger_laplacian (hg : ContDiff ℝ ∞ fun p => schrodinger p g) :
    ContDiff ℝ ∞ fun p => schrodinger p (laplacian g) := by
  rw [funext (schrodinger_laplacian hg)]
  exact ContDiff.sum fun j _ =>
    (contDiff_fderiv_fderiv_mul hg _ _).add (contDiff_fderiv_fderiv_mul hg _ _)

/-! ### The smooth vectors -/

lemma exists_inner_eq_pow_mul_of_contDiff (K : ℕ) :
    ∀ g : 𝓗, (ContDiff ℝ ∞ fun p => schrodinger p g) → ∃ w : 𝓗, ∀ α,
      ⟪hermitePiBasis α, w⟫_ℂ = (oscillatorEigenvalue ι α : ℂ) ^ K * ⟪hermitePiBasis α, g⟫_ℂ := by
  induction K with
  | zero => exact fun g _ => ⟨g, fun α => by simp⟩
  | succ K ih =>
    intro g hg
    obtain ⟨w, hw⟩ := ih (laplacian g) (contDiff_schrodinger_laplacian hg)
    refine ⟨(-2⁻¹ : ℂ) • w, fun α => ?_⟩
    rw [inner_smul_right, hw, inner_hermitePiBasis_laplacian hg, pow_succ]
    ring

/-- **The Schwartz space is the space of smooth vectors of the Schrödinger representation.**
A vector `g ∈ L²(ℝ^ι)`, `ι` nonempty, has a smooth orbit `p ↦ ρ(p) g` under the Schrödinger
representation of the Heisenberg group iff it is a Schwartz function. -/
theorem contDiff_schrodinger_iff [Nonempty ι] (g : 𝓗) :
    (ContDiff ℝ ∞ fun p => schrodinger p g) ↔ ∃ f : 𝓢(Eι, ℂ), f.toLp 2 = g := by
  refine ⟨fun hg => exists_toLp_eq_of_forall_exists_inner fun K =>
    exists_inner_eq_pow_mul_of_contDiff K g hg, ?_⟩
  rintro ⟨f, rfl⟩
  exact contDiff_schrodinger_toLp f

end Heisenberg
