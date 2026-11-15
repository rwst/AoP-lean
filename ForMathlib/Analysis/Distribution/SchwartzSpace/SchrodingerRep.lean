/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Calculus.ParametricLp
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The Schrödinger representation of the Heisenberg group

On `E × E × ℝ`, for a real inner product space `E`, the polarized Heisenberg group law is
`(a, b, t)(a', b', t') = (a + a', b + b', t + t' + ⟪a, b'⟫)`. It acts on `L²(E)` by the unitaries
`ρ(a, b, t) g (x) = e^{i(t + ⟪x, b⟫)} g(x + a)`, and `ρ(p) ρ(q) = ρ(pq)`: this is the Schrödinger
representation (G. B. Folland, *Harmonic Analysis in Phase Space*, Princeton 1989, Ch. 1), here in
the coordinates of R. Goodman (Trans. Amer. Math. Soc. 143 (1969) 55–76, Sec. 6) for one
dimension: translations, modulations and a central phase, with `ħ = 1`.

For a Schwartz function `f`, the orbit `p ↦ ρ(p) f` is a smooth map into `L²(E)`. Its derivative
at `p = (a, b, t)` in the direction `(u, w, s)` is `ρ(p)` applied to the Schwartz function
`∂_u f + i ⟪w, x⟫ f + i (s - ⟪w, a⟫) f`; at `p = 0` the three directions give `∂_u`, the
multiplication by `i ⟪w, x⟫` and `i`. The derivative is obtained by differentiating under the `L²`
norm (`MeasureTheory.hasFDerivAt_toLp_of_dominated`), and the smoothness follows by induction,
since the derivative is again built from orbits of Schwartz functions.

## Main definitions

* `Heisenberg.mul`, `Heisenberg.inv`: the group law of the polarized Heisenberg group;
* `Heisenberg.schrodinger p`: the unitary `ρ(p)` of `L²(E)`;
* `Heisenberg.orbitDeriv f p`: the derivative of the orbit of `f` at `p`.

## Main results

* `Heisenberg.schrodinger_schrodinger`: `ρ(p) ρ(q) = ρ(pq)`;
* `Heisenberg.hasFDerivAt_schrodinger_toLp`: the derivative of the orbit of a Schwartz function;
* `Heisenberg.contDiff_schrodinger_toLp`: the orbit of a Schwartz function is smooth.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Metric Set Complex Module
open scoped Topology ContDiff InnerProductSpace SchwartzMap LineDeriv

namespace Heisenberg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The polarized Heisenberg group -/

/-- The group law `(a, b, t)(a', b', t') = (a + a', b + b', t + t' + ⟪a, b'⟫)` of the polarized
Heisenberg group on `E × E × ℝ`. -/
def mul (p q : E × E × ℝ) : E × E × ℝ :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + ⟪p.1, q.2.1⟫_ℝ)

/-- The inverse `(a, b, t)⁻¹ = (-a, -b, -t + ⟪a, b⟫)`. -/
def inv (p : E × E × ℝ) : E × E × ℝ := (-p.1, -p.2.1, -p.2.2 + ⟪p.1, p.2.1⟫_ℝ)

lemma mul_inv (p : E × E × ℝ) : mul p (inv p) = 0 := by
  simp only [mul, inv, inner_neg_right]
  ext <;> simp

lemma inv_mul (p : E × E × ℝ) : mul (inv p) p = 0 := by
  simp only [mul, inv, inner_neg_left]
  ext <;> simp

lemma inv_smul_fst (t : ℝ) (u : E) :
    inv (t • ((u, 0, 0) : E × E × ℝ)) = t • ((-u, 0, 0) : E × E × ℝ) := by
  ext <;> simp [inv]

lemma inv_smul_snd (t : ℝ) (w : E) :
    inv (t • ((0, w, 0) : E × E × ℝ)) = t • ((0, -w, 0) : E × E × ℝ) := by
  ext <;> simp [inv]

lemma contDiff_mul :
    ContDiff ℝ ∞ fun pq : (E × E × ℝ) × (E × E × ℝ) => mul pq.1 pq.2 := by
  unfold mul
  refine (contDiff_fst.fst.add contDiff_snd.fst).prodMk
    ((contDiff_fst.snd.fst.add contDiff_snd.snd.fst).prodMk
      ((contDiff_fst.snd.snd.add contDiff_snd.snd.snd).add
        (contDiff_fst.fst.inner ℝ contDiff_snd.snd.fst)))

/-! ### The phase -/

/-- The linear form `(u, w, s) ↦ s + ⟪x, w⟫`. -/
def phaseForm (x : E) : E × E × ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ E (E × ℝ)) +
    ((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E ℝ)).comp
      (ContinuousLinearMap.snd ℝ E (E × ℝ))

lemma phaseForm_apply (x : E) (v : E × E × ℝ) : phaseForm x v = v.2.2 + ⟪x, v.2.1⟫_ℝ :=
  rfl

/-- The phase `e^{i(t + ⟪x, b⟫)}` of `ρ(a, b, t)` at `x`. -/
def phase (p : E × E × ℝ) (x : E) : ℂ := cexp ((phaseForm x p : ℂ) * I)

lemma norm_phase (p : E × E × ℝ) (x : E) : ‖phase p x‖ = 1 :=
  norm_exp_ofReal_mul_I _

lemma continuous_phase (p : E × E × ℝ) : Continuous (phase p) := by
  unfold phase
  simp only [phaseForm_apply]
  fun_prop

lemma phase_mul_phase (p q : E × E × ℝ) (x : E) :
    phase p x * phase q (x + p.1) = phase (mul p q) x := by
  simp only [phase, ← Complex.exp_add, phaseForm_apply, mul, inner_add_left, inner_add_right]
  congr 1
  push_cast
  ring

lemma phase_zero (x : E) : phase 0 x = 1 := by
  simp [phase, phaseForm_apply]

/-! ### Multiplication by a linear form -/

/-- Multiplication by `⟪w, x⟫`. -/
def innerMul (w : E) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ fun x : E => ((⟪w, x⟫_ℝ : ℝ) : ℂ)

lemma hasTemperateGrowth_inner (w : E) :
    Function.HasTemperateGrowth fun x : E => ((⟪w, x⟫_ℝ : ℝ) : ℂ) :=
  (ofRealCLM.comp (innerSL ℝ w)).hasTemperateGrowth

@[simp]
lemma innerMul_apply (w : E) (f : 𝓢(E, ℂ)) (x : E) : innerMul w f x = ⟪w, x⟫_ℝ * f x := by
  rw [innerMul, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_inner w), smul_eq_mul]

/-! ### Pointwise orbits of Schwartz functions -/

/-- The orbit of a Schwartz function, pointwise: `e^{i(t + ⟪x, b⟫)} f(x + a)`. -/
def orbitFun (f : 𝓢(E, ℂ)) (p : E × E × ℝ) (x : E) : ℂ := phase p x * f (x + p.1)

/-- The derivative of `p ↦ orbitFun f p x`. -/
def orbitFunDeriv (f : 𝓢(E, ℂ)) (p : E × E × ℝ) (x : E) : E × E × ℝ →L[ℝ] ℂ :=
  phase p x • ((fderiv ℝ f (x + p.1)).comp (ContinuousLinearMap.fst ℝ E (E × ℝ)) +
    (I * f (x + p.1)) • (ofRealCLM.comp (phaseForm x)))

lemma orbitFunDeriv_apply (f : 𝓢(E, ℂ)) (p : E × E × ℝ) (x : E) (v : E × E × ℝ) :
    orbitFunDeriv f p x v =
      phase p x * (fderiv ℝ f (x + p.1) v.1 + I * f (x + p.1) * (phaseForm x v : ℂ)) := by
  simp [orbitFunDeriv, mul_add]

lemma hasFDerivAt_orbitFun (f : 𝓢(E, ℂ)) (p : E × E × ℝ) (x : E) :
    HasFDerivAt (fun q => orbitFun f q x) (orbitFunDeriv f p x) p := by
  have h1 : HasFDerivAt (fun q : E × E × ℝ => phase q x)
      (phase p x • (I • ofRealCLM.comp (phaseForm x))) p :=
    ((ofRealCLM.comp (phaseForm x)).hasFDerivAt.mul_const I).cexp
  have h2 : HasFDerivAt (fun q : E × E × ℝ => f (x + q.1))
      ((fderiv ℝ f (x + p.1)).comp (ContinuousLinearMap.fst ℝ E (E × ℝ))) p :=
    (f.differentiableAt.hasFDerivAt).comp p (hasFDerivAt_fst.const_add x)
  refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [orbitFunDeriv_apply]
  ring

/-- The orbit derivative is bounded by `(1 + ‖x‖) (‖Df‖ + ‖f‖)` at the shifted point. -/
lemma norm_orbitFunDeriv_le (f : 𝓢(E, ℂ)) (p : E × E × ℝ) (x : E) :
    ‖orbitFunDeriv f p x‖ ≤
      (1 + ‖x‖) * (‖fderiv ℝ f (x + p.1)‖ + ‖f (x + p.1)‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [orbitFunDeriv_apply, norm_mul, norm_phase, one_mul]
  have hv1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have hv2 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
  have hv3 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
  have hD : ‖fderiv ℝ f (x + p.1) v.1‖ ≤ ‖fderiv ℝ f (x + p.1)‖ * ‖v‖ :=
    ((fderiv ℝ f (x + p.1)).le_opNorm v.1).trans (by gcongr)
  have hphi : ‖(phaseForm x v : ℂ)‖ ≤ (1 + ‖x‖) * ‖v‖ := by
    rw [Complex.norm_real, phaseForm_apply]
    calc ‖v.2.2 + ⟪x, v.2.1⟫_ℝ‖ ≤ ‖v.2.2‖ + ‖x‖ * ‖v.2.1‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_inner_le_norm _ _)
      _ ≤ ‖v‖ + ‖x‖ * ‖v‖ := by gcongr
      _ = (1 + ‖x‖) * ‖v‖ := by ring
  calc ‖fderiv ℝ f (x + p.1) v.1 + I * f (x + p.1) * (phaseForm x v : ℂ)‖
      ≤ ‖fderiv ℝ f (x + p.1)‖ * ‖v‖ + ‖f (x + p.1)‖ * ((1 + ‖x‖) * ‖v‖) := by
        refine (norm_add_le _ _).trans (add_le_add hD ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
        gcongr
    _ ≤ (1 + ‖x‖) * (‖fderiv ℝ f (x + p.1)‖ + ‖f (x + p.1)‖) * ‖v‖ := by
        have : 0 ≤ ‖x‖ := norm_nonneg _
        have : 0 ≤ ‖v‖ := norm_nonneg _
        have : 0 ≤ ‖fderiv ℝ f (x + p.1)‖ := norm_nonneg _
        nlinarith [mul_nonneg (mul_nonneg this ‹0 ≤ ‖x‖›) ‹0 ≤ ‖v‖›]

/-- The direction part of the orbit derivative at `(a, b, t)`:
`(u, w, s) ↦ ∂_u f + i ⟪w, x⟫ f + i (s - ⟪w, a⟫) f`. -/
def derivDir (f : 𝓢(E, ℂ)) (a : E) : E × E × ℝ →ₗ[ℝ] 𝓢(E, ℂ) where
  toFun v := ∂_{v.1} f + I • innerMul v.2.1 f + (I * ((v.2.2 - ⟪v.2.1, a⟫_ℝ : ℝ) : ℂ)) • f
  map_add' v v' := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, _root_.add_apply, _root_.smul_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, map_add, innerMul_apply, inner_add_left,
      smul_eq_mul]
    push_cast
    ring
  map_smul' c v := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, _root_.add_apply, _root_.smul_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, map_smul, innerMul_apply, inner_smul_left,
      smul_eq_mul, RingHom.id_apply, Complex.real_smul, conj_trivial]
    push_cast
    ring

lemma derivDir_apply_apply (f : 𝓢(E, ℂ)) (a : E) (v : E × E × ℝ) (x : E) :
    derivDir f a v x = fderiv ℝ f x v.1 + I * ⟪v.2.1, x⟫_ℝ * f x +
      I * ((v.2.2 - ⟪v.2.1, a⟫_ℝ : ℝ) : ℂ) * f x := by
  simp [derivDir, SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_assoc]

lemma derivDir_fst (f : 𝓢(E, ℂ)) (a u : E) : derivDir f a (u, 0, 0) = ∂_{u} f := by
  ext x
  simp [derivDir_apply_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

lemma derivDir_snd (f : 𝓢(E, ℂ)) (w : E) : derivDir f 0 (0, w, 0) = I • innerMul w f := by
  ext x
  simp [derivDir_apply_apply, mul_assoc]

/-! ### The Schrödinger representation on `L²` -/

variable [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

set_option hygiene false in
local notation "𝓗" => Lp ℂ 2 (volume : Measure E)

lemma memLp_phase_mul (p : E × E × ℝ) {g : E → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun x => phase p x * g (x + p.1)) 2 volume := by
  have h := hg.comp_measurePreserving (measurePreserving_add_right volume p.1)
  refine h.congr_norm ((continuous_phase p).aestronglyMeasurable.mul h.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp [norm_phase]

/-- `g ↦ e^{i(t + ⟪x, b⟫)} g(x + a)` on `L²`. -/
def schrodingerFun (p : E × E × ℝ) (g : 𝓗) : 𝓗 :=
  (memLp_phase_mul p (Lp.memLp g)).toLp _

lemma coeFn_schrodingerFun (p : E × E × ℝ) (g : 𝓗) :
    schrodingerFun p g =ᵐ[volume] fun x => phase p x * g (x + p.1) :=
  MemLp.coeFn_toLp _

omit [InnerProductSpace ℝ E] in
lemma ae_comp_add (a : E) {g₁ g₂ : E → ℂ} (h : g₁ =ᵐ[volume] g₂) :
    (fun x => g₁ (x + a)) =ᵐ[volume] fun x => g₂ (x + a) :=
  (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp h

lemma schrodingerFun_schrodingerFun (p q : E × E × ℝ) (g : 𝓗) :
    schrodingerFun p (schrodingerFun q g) = schrodingerFun (mul p q) g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_schrodingerFun p (schrodingerFun q g),
    ae_comp_add p.1 (coeFn_schrodingerFun q g), coeFn_schrodingerFun (mul p q) g] with x h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, phase_mul_phase, add_assoc]
  rfl

lemma schrodingerFun_zero (g : 𝓗) : schrodingerFun 0 g = g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_schrodingerFun 0 g] with x h
  rw [h, phase_zero, one_mul]
  simp

/-- **The Schrödinger representation** `ρ(a, b, t) g (x) = e^{i(t + ⟪x, b⟫)} g(x + a)`, a unitary
of `L²(E)`. -/
def schrodinger (p : E × E × ℝ) : 𝓗 ≃ₗᵢ[ℂ] 𝓗 where
  toFun := schrodingerFun p
  invFun := schrodingerFun (inv p)
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_schrodingerFun p (f + g), coeFn_schrodingerFun p f,
      coeFn_schrodingerFun p g, Lp.coeFn_add (schrodingerFun p f) (schrodingerFun p g),
      ae_comp_add p.1 (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_schrodingerFun p (c • f), coeFn_schrodingerFun p f,
      Lp.coeFn_smul c (schrodingerFun p f), ae_comp_add p.1 (Lp.coeFn_smul c f)]
      with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, mul_left_comm]
  left_inv g := by
    rw [schrodingerFun_schrodingerFun, inv_mul, schrodingerFun_zero]
  right_inv g := by
    rw [schrodingerFun_schrodingerFun, mul_inv, schrodingerFun_zero]
  norm_map' g := by
    change ‖schrodingerFun p g‖ = ‖g‖
    have hm := measurePreserving_add_right (volume : Measure E) p.1
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae (g := (g : E → ℂ) ∘ (· + p.1))
      (Lp.aestronglyMeasurable _) ((Lp.aestronglyMeasurable g).comp_measurePreserving hm),
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable g) hm]
    filter_upwards [coeFn_schrodingerFun p g] with x hx
    rw [hx, norm_mul, norm_phase, one_mul, Function.comp_apply]

lemma schrodinger_apply (p : E × E × ℝ) (g : 𝓗) : schrodinger p g = schrodingerFun p g :=
  rfl

lemma coeFn_schrodinger (p : E × E × ℝ) (g : 𝓗) :
    schrodinger p g =ᵐ[volume] fun x => phase p x * g (x + p.1) :=
  coeFn_schrodingerFun p g

lemma schrodinger_symm (p : E × E × ℝ) : (schrodinger p).symm = schrodinger (inv p) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- `ρ` is a representation: `ρ(p) ρ(q) = ρ(pq)`. -/
theorem schrodinger_schrodinger (p q : E × E × ℝ) (g : 𝓗) :
    schrodinger p (schrodinger q g) = schrodinger (mul p q) g :=
  schrodingerFun_schrodingerFun p q g

@[simp]
lemma schrodinger_zero (g : 𝓗) : schrodinger 0 g = g :=
  schrodingerFun_zero g

/-- `ρ(p)* = ρ(p⁻¹)`. -/
lemma inner_schrodinger_right (p : E × E × ℝ) (h g : 𝓗) :
    ⟪h, schrodinger p g⟫_ℂ = ⟪schrodinger (inv p) h, g⟫_ℂ := by
  rw [← schrodinger_symm, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]

/-! ### Orbits of Schwartz functions -/

variable [FiniteDimensional ℝ E]

lemma memLp_orbitFun (f : 𝓢(E, ℂ)) (p : E × E × ℝ) : MemLp (orbitFun f p) 2 volume :=
  memLp_phase_mul p (f.memLp 2 volume)

lemma coeFn_schrodinger_toLp (f : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    schrodinger p (f.toLp 2) =ᵐ[volume] orbitFun f p := by
  filter_upwards [coeFn_schrodinger p (f.toLp 2), ae_comp_add p.1 (f.coeFn_toLp 2 volume)]
    with x h1 h2
  rw [h1, h2, orbitFun]

lemma schrodinger_toLp_eq (f : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    schrodinger p (f.toLp 2) = (memLp_orbitFun f p).toLp _ :=
  Lp.ext ((coeFn_schrodinger_toLp f p).trans (memLp_orbitFun f p).coeFn_toLp.symm)

/-- `(1 + ‖x‖)^{-N}` is square integrable for `2N > dim E`. -/
lemma memLp_inv_one_add_norm_pow {N : ℕ} (hN : finrank ℝ E < 2 * N) :
    MemLp (fun x : E => ((1 + ‖x‖) ^ N)⁻¹) 2 volume := by
  have hm : AEStronglyMeasurable (fun x : E => ((1 + ‖x‖) ^ N)⁻¹) volume := by fun_prop
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine (integrable_one_add_norm (E := E) (μ := volume) (r := 2 * N)
    (by exact_mod_cast hN)).congr (ae_of_all _ fun x => ?_)
  have h0 : 0 ≤ 1 + ‖x‖ := by positivity
  show (1 + ‖x‖) ^ (-(2 * (N : ℝ))) = ((1 + ‖x‖) ^ N)⁻¹ ^ 2
  rw [Real.rpow_neg h0, inv_pow, ← pow_mul, mul_comm N 2]
  norm_cast

/-- A uniform bound for the orbit derivative near `p`. -/
lemma exists_norm_orbitFunDeriv_le (f : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    ∃ B : E → ℝ, MemLp B 2 volume ∧ ∀ x, ∀ q ∈ ball p 1, ‖orbitFunDeriv f q x‖ ≤ B x := by
  set N := finrank ℝ E + 1
  set c := 2 + ‖p.1‖
  set S := (Finset.Iic (N + 1, 1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  set K := c ^ (N + 1) * (2 * (2 ^ (N + 1) * S))
  refine ⟨fun x => K * ((1 + ‖x‖) ^ N)⁻¹, (memLp_inv_one_add_norm_pow (by omega)).const_mul K,
    fun x q hq => (norm_orbitFunDeriv_le f q x).trans ?_⟩
  set y := x + q.1
  have hq1 : ‖q.1‖ ≤ ‖p.1‖ + 1 := by
    have : ‖q.1 - p.1‖ ≤ ‖q - p‖ := norm_fst_le (q - p)
    rw [mem_ball, dist_eq_norm] at hq
    linarith [norm_sub_norm_le q.1 p.1]
  have hx : 1 + ‖x‖ ≤ c * (1 + ‖y‖) := by
    have : ‖x‖ ≤ ‖y‖ + ‖q.1‖ := by
      have := norm_sub_le y q.1
      rwa [show y - q.1 = x by simp [y]] at this
    have : 0 ≤ ‖p.1‖ * ‖y‖ := by positivity
    simp only [c]
    nlinarith [norm_nonneg y]
  have hS0 : (1 + ‖y‖) ^ (N + 1) * ‖f y‖ ≤ 2 ^ (N + 1) * S := by
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 1, 1)) le_rfl
        (zero_le_one) f y
  have hS1 : (1 + ‖y‖) ^ (N + 1) * ‖fderiv ℝ f y‖ ≤ 2 ^ (N + 1) * S := by
    simpa [norm_iteratedFDeriv_one] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 1, 1)) le_rfl le_rfl f y
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  show _ ≤ K * ((1 + ‖x‖) ^ N)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  calc (1 + ‖x‖) * (‖fderiv ℝ f y‖ + ‖f y‖) * (1 + ‖x‖) ^ N
      = (1 + ‖x‖) ^ (N + 1) * (‖fderiv ℝ f y‖ + ‖f y‖) := by ring
    _ ≤ (c * (1 + ‖y‖)) ^ (N + 1) * (‖fderiv ℝ f y‖ + ‖f y‖) := by gcongr
    _ = c ^ (N + 1) * ((1 + ‖y‖) ^ (N + 1) * ‖fderiv ℝ f y‖ +
          (1 + ‖y‖) ^ (N + 1) * ‖f y‖) := by rw [mul_pow]; ring
    _ ≤ c ^ (N + 1) * (2 ^ (N + 1) * S + 2 ^ (N + 1) * S) := by gcongr
    _ = K := by ring

/-- The derivative at `p` of the orbit `p ↦ ρ(p) f` of a Schwartz function `f`. -/
def orbitDeriv (f : 𝓢(E, ℂ)) (p : E × E × ℝ) : E × E × ℝ →L[ℝ] 𝓗 :=
  (((schrodinger p).toLinearIsometry.toContinuousLinearMap.comp
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume)).restrictScalars ℝ).comp
      (derivDir f p.1).toContinuousLinearMap

lemma orbitDeriv_apply (f : 𝓢(E, ℂ)) (p v : E × E × ℝ) :
    orbitDeriv f p v = schrodinger p ((derivDir f p.1 v).toLp 2) :=
  rfl

/-- **The derivative of a Schwartz orbit.** `p ↦ ρ(p) f` has at `p = (a, b, t)` the derivative
`(u, w, s) ↦ ρ(p) (∂_u f + i ⟪w, x⟫ f + i (s - ⟪w, a⟫) f)`. -/
theorem hasFDerivAt_schrodinger_toLp (f : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    HasFDerivAt (fun q => schrodinger q (f.toLp 2)) (orbitDeriv f p) p := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_orbitFunDeriv_le f p
  have h := hasFDerivAt_toLp_of_dominated ENNReal.ofNat_ne_top one_pos (memLp_orbitFun f)
    hB (fun x q _ => hasFDerivAt_orbitFun f q x) hbound (L := orbitDeriv f p) fun v => by
      rw [orbitDeriv_apply]
      filter_upwards [coeFn_schrodinger_toLp (derivDir f p.1 v) p] with x hx
      rw [hx, orbitFun, orbitFunDeriv_apply, derivDir_apply_apply, phaseForm_apply,
        inner_add_right, real_inner_comm x]
      push_cast
      ring
  simpa only [← schrodinger_toLp_eq] using h

lemma schrodinger_toLp_add (f g : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    schrodinger p ((f + g).toLp 2) = schrodinger p (f.toLp 2) + schrodinger p (g.toLp 2) := by
  rw [← map_add, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_add]
  rfl

lemma schrodinger_toLp_smul (c : ℂ) (f : 𝓢(E, ℂ)) (p : E × E × ℝ) :
    schrodinger p ((c • f).toLp 2) = c • schrodinger p (f.toLp 2) := by
  rw [← map_smul, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_smul]
  rfl

/-- **Schwartz functions are smooth vectors.** The orbit `p ↦ ρ(p) f` of a Schwartz function is
a smooth map into `L²`. -/
theorem contDiff_schrodinger_toLp (f : 𝓢(E, ℂ)) :
    ContDiff ℝ ∞ fun p => schrodinger p (f.toLp 2) := by
  refine contDiff_infty.2 fun n => ?_
  induction n generalizing f with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_schrodinger_toLp f p).continuousAt)
  | succ n ih =>
    refine contDiff_succ_iff_hasFDerivAt.2
      ⟨orbitDeriv f, ?_, hasFDerivAt_schrodinger_toLp f⟩
    refine contDiff_clm_apply_iff.2 fun v => ?_
    set f₁ : 𝓢(E, ℂ) := ∂_{v.1} f + I • innerMul v.2.1 f + (I * (v.2.2 : ℂ)) • f
    have hd : ∀ p : E × E × ℝ, derivDir f p.1 v = f₁ + (-(I * (⟪v.2.1, p.1⟫_ℝ : ℂ))) • f := by
      intro p
      ext x
      simp only [derivDir_apply_apply, f₁, _root_.add_apply, _root_.smul_apply,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, innerMul_apply, smul_eq_mul]
      push_cast
      ring
    have : (fun p => orbitDeriv f p v) = fun p =>
        schrodinger p (f₁.toLp 2) + (-(I * (⟪v.2.1, p.1⟫_ℝ : ℂ))) • schrodinger p (f.toLp 2) :=
      funext fun p => by rw [orbitDeriv_apply, hd, schrodinger_toLp_add, schrodinger_toLp_smul]
    have hc : ContDiff ℝ n fun p : E × E × ℝ => -(I * ((⟪v.2.1, p.1⟫_ℝ : ℝ) : ℂ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_const.inner ℝ contDiff_fst))).neg
    rw [this]
    exact (ih f₁).add (hc.smul (ih f))

/-- **The generators on `𝓢`.** At `p = 0` the orbit of a Schwartz function has the derivative
`(u, w, s) ↦ ∂_u f + i ⟪w, x⟫ f + i s f`. -/
theorem fderiv_schrodinger_toLp_zero (f : 𝓢(E, ℂ)) (v : E × E × ℝ) :
    fderiv ℝ (fun p => schrodinger p (f.toLp 2)) 0 v =
      (∂_{v.1} f + I • innerMul v.2.1 f + (I * (v.2.2 : ℂ)) • f).toLp 2 := by
  rw [(hasFDerivAt_schrodinger_toLp f 0).fderiv, orbitDeriv_apply, schrodinger_zero]
  congr 1
  ext x
  simp [derivDir_apply_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_assoc]

/-! ### Lines through `0` in the directions of `a` and of `b` -/

lemma hasDerivAt_schrodinger_toLp_smul (f : 𝓢(E, ℂ)) (v : E × E × ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodinger (s • v) (f.toLp 2))
      (schrodinger (t • v) ((derivDir f (t • v).1 v).toLp 2)) t := by
  have := (hasFDerivAt_schrodinger_toLp f (t • v)).comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const v)
  simpa only [orbitDeriv_apply, one_smul, Function.comp_def, id] using this

/-- Along the direction `(u, 0, 0)` the orbit of `f` has the derivative `ρ(t u, 0, 0) ∂_u f`. -/
lemma hasDerivAt_schrodinger_toLp_fst (f : 𝓢(E, ℂ)) (u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodinger (s • ((u, 0, 0) : E × E × ℝ)) (f.toLp 2))
      (schrodinger (t • ((u, 0, 0) : E × E × ℝ)) ((∂_{u} f).toLp 2)) t := by
  have h := hasDerivAt_schrodinger_toLp_smul f (u, 0, 0) t
  rwa [derivDir_fst] at h

/-- Along the direction `(0, w, 0)` the orbit of `f` has the derivative
`ρ(0, t w, 0) (i ⟪w, x⟫ f)`. -/
lemma hasDerivAt_schrodinger_toLp_snd (f : 𝓢(E, ℂ)) (w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodinger (s • ((0, w, 0) : E × E × ℝ)) (f.toLp 2))
      (schrodinger (t • ((0, w, 0) : E × E × ℝ)) ((I • innerMul w f).toLp 2)) t := by
  have h := hasDerivAt_schrodinger_toLp_smul f (0, w, 0) t
  rwa [show (t • ((0, w, 0) : E × E × ℝ)).1 = 0 by simp, derivDir_snd] at h

end Heisenberg
