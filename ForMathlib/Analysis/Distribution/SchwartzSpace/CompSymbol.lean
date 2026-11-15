/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.Multiplier
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Composition operators on Schwartz space (Galbis–Jordá)

Galbis and Jordá [Composition operators on the Schwartz space, Rev. Mat. Iberoam. 34 (2018),
Thm. 2.3 and Remark 2.4] characterize the smooth maps `φ` between Euclidean spaces for which
`f ∘ φ` is a Schwartz function for every Schwartz function `f`. This file proves their theorem for
`φ : D → E` with `D` any real normed space, `E` finite-dimensional, and values in any real normed
space `F ≠ 0`. The condition is

* (i) every derivative of `φ` is bounded by a power of `1 + ‖φ‖`, and
* (ii) `‖x‖` is bounded by a power of `1 + ‖φ x‖`.

The paper states (i) with powers of `1 + ‖φ‖²` and (ii) as `‖φ x‖ ≥ ‖x‖^{1/k}` for `‖x‖ ≥ k`;
both forms are equivalent to the ones here. Condition (i) is weaker than temperate growth:
`x ↦ exp (x ^ 2)` satisfies it. Mathlib's `SchwartzMap.compCLM` assumes temperate growth and (ii).

Sufficiency is the proof of `SchwartzMap.compCLM` with `1 + ‖φ x‖` in place of `1 + ‖x‖`. For
necessity, if a bound fails along a sequence `x j`, either `φ (x j)` stays bounded along a
subsequence, and a single bump detects the failure, or it runs to infinity, and bumps glued along a
separated subsequence (`SchwartzMap.exists_eqOn_ball_smul`) do. The paper's bumps have prescribed
derivatives at `0`, and its argument uses Faà di Bruno's formula; here the bumps are linear near
their centres, so `f ∘ φ` is linear in `φ` there and its `n`-th derivative is read off directly.
Nothing about `D` beyond being a real normed space is used.

## Main definitions

* `SchwartzMap.compSymbolCLM`: `f ↦ f ∘ φ` as a continuous linear map, under (i) and (ii).

## Main results

* `SchwartzMap.forall_exists_comp_iff`: the Galbis–Jordá characterization;
* `SchwartzMap.forall_exists_comp_equiv_iff`: for a bijection `e` with `e`, `e⁻¹` smooth,
  `f ↦ f ∘ e` maps `𝓢(E, F)` onto `𝓢(D, F)` if and only if `e` and `e⁻¹` have temperate growth.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology ContDiff

namespace SchwartzMap

variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Sufficiency -/

section Sufficiency

/-- A bound of type (i) for all orders up to `n` at once. -/
private lemma exists_uniform {φ : D → E}
    (hderiv : ∀ n, ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l)
    (n : ℕ) : ∃ (l : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ N ≤ n, ∀ x, ‖iteratedFDeriv ℝ N φ x‖ ≤ C * (1 + ‖φ x‖) ^ l := by
  induction n with
  | zero =>
    obtain ⟨l, C, h⟩ := hderiv 0
    refine ⟨l, |C|, abs_nonneg _, fun N hN x => ?_⟩
    rw [Nat.le_zero.1 hN]
    exact (h x).trans (by gcongr; exact le_abs_self C)
  | succ n ih =>
    obtain ⟨l₁, C₁, hC₁, h₁⟩ := ih
    obtain ⟨l₂, C₂, h₂⟩ := hderiv (n + 1)
    refine ⟨max l₁ l₂, max C₁ |C₂|, le_max_of_le_left hC₁, fun N hN x => ?_⟩
    have h1 : 1 ≤ 1 + ‖φ x‖ := le_add_of_nonneg_right (norm_nonneg _)
    rcases Nat.lt_or_eq_of_le hN with hN | rfl
    · exact (h₁ N (Nat.lt_succ_iff.1 hN) x).trans (mul_le_mul (le_max_left _ _)
        (pow_le_pow_right₀ h1 (le_max_left _ _)) (by positivity) (le_max_of_le_left hC₁))
    · exact (h₂ x).trans (mul_le_mul ((le_abs_self _).trans (le_max_right _ _))
        (pow_le_pow_right₀ h1 (le_max_right _ _)) (by positivity) (le_max_of_le_left hC₁))

variable (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]

/-- **Composition with a symbol.** If `φ` is smooth, every derivative of `φ` is bounded by a power
of `1 + ‖φ‖`, and `‖x‖` is bounded by a power of `1 + ‖φ x‖`, then `f ↦ f ∘ φ` is a continuous
linear map `𝓢(E, F) → 𝓢(D, F)`. The proof is that of `SchwartzMap.compCLM`. -/
def compSymbolCLM {φ : D → E} (hφ : ContDiff ℝ ∞ φ)
    (hderiv : ∀ n, ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l)
    (hupper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖φ x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F) :=
  mkCLM (fun f => f ∘ φ) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
    (fun f => (f.smooth ⊤).comp hφ) <| by
  rintro ⟨k, n⟩
  obtain ⟨l, C, hC, hgrowth⟩ := exists_uniform hderiv n
  obtain ⟨kg, Cg, hg_upper⟩ := hupper
  have hCg : 1 ≤ 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    have := hg_upper 0
    rw [norm_zero] at this
    exact nonneg_of_mul_nonneg_left this (by positivity)
  let k' := kg * k + l * n
  refine ⟨Finset.Iic (k', n), (1 + Cg) ^ k * ((C + 1) ^ n * n.factorial * 2 ^ k'),
    mul_nonneg (pow_nonneg (by linarith) _) (by positivity), fun f x => ?_⟩
  set s := (Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 E F) f
  have h1 : 1 ≤ 1 + ‖φ x‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hpos : 0 < (1 + ‖φ x‖) ^ k' := by positivity
  have hx : ‖x‖ ^ k ≤ (1 + Cg) ^ k * (1 + ‖φ x‖) ^ (kg * k) := by
    rw [pow_mul, ← mul_pow]
    gcongr
    calc ‖x‖ ≤ Cg * (1 + ‖φ x‖) ^ kg := hg_upper x
      _ ≤ (1 + Cg) * (1 + ‖φ x‖) ^ kg := by gcongr; linarith
  have hbound (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (φ x)‖ ≤ 2 ^ k' * s / (1 + ‖φ x‖) ^ k' := by
    rw [le_div_iff₀' hpos]
    change i ≤ (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
      ‖iteratedFDeriv ℝ N φ x‖ ≤ ((C + 1) * (1 + ‖φ x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    calc C * (1 + ‖φ x‖) ^ l ≤ (C + 1) * (1 + ‖φ x‖) ^ l := by gcongr; linarith
      _ ≤ _ := le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ h1))
          (by omega)
  have hcomp := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hφ (mod_cast le_top) x hbound hgrowth'
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f ∘ φ) x‖
      ≤ ((1 + Cg) ^ k * (1 + ‖φ x‖) ^ (kg * k)) *
          (n.factorial * (2 ^ k' * s / (1 + ‖φ x‖) ^ k') * ((C + 1) * (1 + ‖φ x‖) ^ l) ^ n) :=
        mul_le_mul hx hcomp (by positivity) (mul_nonneg (pow_nonneg (by linarith) _)
          (by positivity))
    _ = (1 + Cg) ^ k * ((C + 1) ^ n * n.factorial * 2 ^ k') * s := by
      rw [show k' = kg * k + l * n from rfl, mul_pow, ← pow_mul, pow_add] at *
      field_simp
      ring

@[simp] lemma compSymbolCLM_apply {φ : D → E} (hφ : ContDiff ℝ ∞ φ)
    (hderiv : ∀ n, ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l)
    (hupper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖φ x‖) ^ k) (f : 𝓢(E, F)) :
    compSymbolCLM 𝕜 hφ hderiv hupper f = f ∘ φ :=
  rfl

end Sufficiency

/-! ### Necessity -/

section Necessity

/-- If `((1 + t)^j)⁻¹ ≤ c`, `j ≤ m` and `m (1 + t)^m < X`, then `j < c X`. -/
private lemma lt_mul_of_inv_pow_le {t c X : ℝ} {j m : ℕ} (ht : 0 ≤ t) (hjm : j ≤ m)
    (hc : ((1 + t) ^ j)⁻¹ ≤ c) (hX : m * (1 + t) ^ m < X) : (j : ℝ) < c * X := by
  have h1 : 1 ≤ 1 + t := by linarith
  have hpos : 0 < (1 + t) ^ j := by positivity
  have hle : (j : ℝ) * (1 + t) ^ j ≤ m * (1 + t) ^ m :=
    mul_le_mul (mod_cast hjm) (pow_le_pow_right₀ h1 hjm) hpos.le (by positivity)
  have hX0 : 0 ≤ X := (by positivity : (0 : ℝ) ≤ m * (1 + t) ^ m).trans hX.le
  calc (j : ℝ) = ((1 + t) ^ j)⁻¹ * (j * (1 + t) ^ j) := by field_simp
    _ < ((1 + t) ^ j)⁻¹ * X := by gcongr; exact hle.trans_lt hX
    _ ≤ c * X := by gcongr

/-- A smooth map that satisfies (i) and grows at most polynomially has temperate growth. -/
private lemma hasTemperateGrowth_of_le {φ : D → E} (hφ : ContDiff ℝ ∞ φ)
    (hderiv : ∀ n, ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l)
    (hup : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖φ x‖ ≤ C * (1 + ‖x‖) ^ k) : φ.HasTemperateGrowth := by
  refine ⟨hφ, fun n => ?_⟩
  obtain ⟨l, C, hC⟩ := hderiv n
  obtain ⟨k, C', hC'⟩ := hup
  refine ⟨k * l, |C| * (1 + |C'|) ^ l, fun x => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hφx : 1 + ‖φ x‖ ≤ (1 + |C'|) * (1 + ‖x‖) ^ k := by
    have hk := one_le_pow₀ (n := k) h1
    nlinarith [hC' x, le_abs_self C', abs_nonneg C']
  calc ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l := hC x
    _ ≤ |C| * ((1 + |C'|) * (1 + ‖x‖) ^ k) ^ l := by
        gcongr
        exact le_abs_self C
    _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]

private lemma exists_norm_le_of_hasTemperateGrowth_symm (u : D ≃ E)
    (hu : (u.symm : E → D).HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖u x‖) ^ k := by
  obtain ⟨k, C, hC⟩ := hu.2 0
  exact ⟨k, C, fun x => by simpa using hC (u x)⟩

variable [FiniteDimensional ℝ E]

/-- The norm of a multilinear map into `E` is controlled by its compositions with the maps
`v ↦ b.coord i v • a`, for a basis `b` and `‖a‖ = 1`. -/
private lemma norm_le_sum_norm_smulRight_comp {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {a : F} (ha : ‖a‖ = 1) {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => D) E) :
    ‖M‖ ≤ ∑ i, ‖b i‖ * ‖((LinearMap.toContinuousLinearMap (b.coord i)).smulRight a)
      |>.compContinuousMultilinearMap M‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  calc ‖M v‖ = ‖∑ i, b.repr (M v) i • b i‖ := by rw [b.sum_repr]
    _ ≤ ∑ i, ‖b.repr (M v) i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ * ‖((LinearMap.toContinuousLinearMap (b.coord i)).smulRight a)
          |>.compContinuousMultilinearMap M‖ * ∏ k, ‖v k‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, mul_comm, mul_assoc]
      gcongr
      have := (((LinearMap.toContinuousLinearMap (b.coord i)).smulRight a)
        |>.compContinuousMultilinearMap M).le_opNorm v
      simpa [ha, norm_smul] using this
    _ = _ := by rw [Finset.sum_mul]

/-- **Test functions along a sequence.** For every sequence `y` in `E` there are a subsequence
`y ∘ τ`, coefficients `c j ≥ (1 + ‖y (τ j)‖)^{-j}` and centres `z j` such that for every smooth
`ψ : E → F` some Schwartz function equals `c j • ψ (· - z j)` near `y (τ j)`, for every `j`. -/
theorem exists_strictMono_testFunctions (y : ℕ → E) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ (c : ℕ → ℝ) (z : ℕ → E),
      (∀ j, ((1 + ‖y (τ j)‖) ^ j)⁻¹ ≤ c j) ∧ ∀ ψ : E → F, ContDiff ℝ ∞ ψ →
        ∃ f : 𝓢(E, F), ∀ j, ∀ᶠ w in 𝓝 (y (τ j)), f w = c j • ψ (w - z j) := by
  by_cases hy : Tendsto (fun j => ‖y j‖) atTop atTop
  · -- The points run to infinity: glue bumps along a separated subsequence.
    obtain ⟨τ, hτ, hsep⟩ := exists_strictMono_pairwise_one_le hy
    refine ⟨τ, hτ, fun j => ((1 + ‖y (τ j)‖) ^ j)⁻¹, fun j => y (τ j), fun j => le_rfl,
      fun ψ hψ => ?_⟩
    let χ : ContDiffBump (0 : E) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
    let ρ : 𝓢(E, F) := (χ.hasCompactSupport.smul_right (f' := ψ)).toSchwartzMap
      (χ.contDiff.smul hψ)
    have hρ : tsupport ρ ⊆ closedBall 0 (1 / 4) :=
      (tsupport_smul_subset_left _ _).trans χ.tsupport_eq.subset
    obtain ⟨f, hf⟩ := exists_eqOn_ball_smul (by norm_num : (1 / 4 : ℝ) < 1 / 2) hρ hsep
      (exists_abs_inv_pow_mul_le (fun j => y (τ j)))
    refine ⟨f, fun j => ?_⟩
    filter_upwards [ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 8)] with w hw
    rw [hf j (ball_subset_ball (by norm_num) hw)]
    have hw' : w - y (τ j) ∈ closedBall (0 : E) χ.rIn := by
      rw [mem_closedBall, dist_eq_norm, sub_zero, ← dist_eq_norm]
      exact (mem_ball.1 hw).le
    simp [ρ, χ.one_of_mem_closedBall hw']
  · -- Otherwise a subsequence stays bounded: one bump suffices.
    simp only [Filter.tendsto_atTop, not_forall, not_eventually, not_le] at hy
    obtain ⟨R, hR⟩ := hy
    obtain ⟨τ, hτ, hτR⟩ := extraction_of_frequently_atTop hR
    refine ⟨τ, hτ, fun _ => 1, fun _ => 0,
      fun j => inv_le_one_of_one_le₀ (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))),
      fun ψ hψ => ?_⟩
    let χ : ContDiffBump (0 : E) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
    let f : 𝓢(E, F) := (χ.hasCompactSupport.smul_right (f' := ψ)).toSchwartzMap
      (χ.contDiff.smul hψ)
    refine ⟨f, fun j => ?_⟩
    have hyj : y (τ j) ∈ ball (0 : E) χ.rIn := by
      change y (τ j) ∈ ball (0 : E) (|R| + 1)
      rw [mem_ball, dist_zero_right]
      linarith [hτR j, le_abs_self R]
    filter_upwards [isOpen_ball.mem_nhds hyj] with w hw
    simp [f, χ.one_of_mem_closedBall (ball_subset_closedBall hw)]

variable [Nontrivial F]

/-- **Galbis–Jordá, necessity of (ii).** If `f ∘ φ` is a Schwartz function for every Schwartz
function `f`, then `‖x‖` is bounded by a power of `1 + ‖φ x‖`. -/
theorem exists_norm_le_of_forall_exists_comp {φ : D → E}
    (h : ∀ f : 𝓢(E, F), ∃ g : 𝓢(D, F), ∀ x, g x = f (φ x)) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖φ x‖) ^ k := by
  by_contra hcon
  push Not at hcon
  choose x hx using fun j : ℕ => hcon j j
  obtain ⟨τ, hτ, c, z, hc, htest⟩ := exists_strictMono_testFunctions (F := F) fun j => φ (x j)
  obtain ⟨a, ha⟩ := exists_norm_eq F zero_le_one
  obtain ⟨f, hf⟩ := htest (fun _ => a) contDiff_const
  obtain ⟨g, hg⟩ := h f
  obtain ⟨C, -, hC⟩ := g.decay 1 0
  obtain ⟨j, hj⟩ := exists_nat_gt C
  have hcj : 0 ≤ c j := le_trans (by positivity : (0 : ℝ) ≤ ((1 + ‖φ (x (τ j))‖) ^ j)⁻¹) (hc j)
  have hgx : g (x (τ j)) = c j • a := by rw [hg]; exact (hf j).self_of_nhds
  have hle := hC (x (τ j))
  rw [pow_one, norm_iteratedFDeriv_zero, hgx, norm_smul, ha, mul_one, Real.norm_of_nonneg hcj,
    mul_comm] at hle
  have hbig := lt_mul_of_inv_pow_le (j := j) (norm_nonneg _) (hτ.id_le j) (hc j) (hx (τ j))
  linarith

/-- **Galbis–Jordá, necessity of (i).** If `φ` is smooth and `f ∘ φ` is a Schwartz function for
every Schwartz function `f`, then every derivative of `φ` is bounded by a power of `1 + ‖φ‖`. -/
theorem exists_norm_iteratedFDeriv_le_of_forall_exists_comp {φ : D → E} (hφ : ContDiff ℝ ∞ φ)
    (h : ∀ f : 𝓢(E, F), ∃ g : 𝓢(D, F), ∀ x, g x = f (φ x)) (n : ℕ) :
    ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, fun x => by rw [norm_iteratedFDeriv_zero, pow_one, one_mul]; linarith⟩
  by_contra hcon
  push Not at hcon
  choose x hx using fun j : ℕ => hcon j j
  obtain ⟨τ, hτ, c, z, hc, htest⟩ := exists_strictMono_testFunctions (F := F) fun j => φ (x j)
  obtain ⟨a, ha⟩ := exists_norm_eq F zero_le_one
  let b := Module.finBasis ℝ E
  let L : Fin (Module.finrank ℝ E) → E →L[ℝ] F := fun i =>
    (LinearMap.toContinuousLinearMap (b.coord i)).smulRight a
  choose f hf using fun i => htest (L i) (L i).contDiff
  choose g hg using fun i => h (f i)
  choose C hC0 hC using fun i => (g i).decay 0 n
  obtain ⟨j, hj⟩ := exists_nat_gt (∑ i, ‖b i‖ * C i)
  have hcj : 0 ≤ c j := le_trans (by positivity : (0 : ℝ) ≤ ((1 + ‖φ (x (τ j))‖) ^ j)⁻¹) (hc j)
  set M := iteratedFDeriv ℝ n φ (x (τ j))
  -- Near `x (τ j)`, `g i = c j • (L i ∘ φ - L i (z j))`, so `Dⁿ(g i) = c j • (L i ∘ Dⁿφ)`.
  have hi : ∀ i, c j * ‖(L i).compContinuousMultilinearMap M‖ ≤ C i := by
    intro i
    have hloc : (g i : D → F) =ᶠ[𝓝 (x (τ j))] c j • ((L i ∘ φ) - fun _ => L i (z j)) := by
      filter_upwards [(hφ.continuous.tendsto (x (τ j))).eventually (hf i j)] with w hw
      rw [hg, hw, map_sub]
      rfl
    have hLφ : ContDiffAt ℝ n (L i ∘ φ) (x (τ j)) :=
      ((L i).contDiff.comp (hφ.of_le (mod_cast le_top))).contDiffAt
    have hle := hC i (x (τ j))
    rw [pow_zero, one_mul, (hloc.iteratedFDeriv ℝ n).eq_of_nhds,
      iteratedFDeriv_const_smul_apply (f := (L i ∘ φ) - fun _ => L i (z j))
        (hLφ.sub contDiffAt_const),
      iteratedFDeriv_sub_apply hLφ contDiffAt_const, iteratedFDeriv_const_of_ne hn.ne',
      Pi.zero_apply, sub_zero,
      (L i).iteratedFDeriv_comp_left (hφ.of_le (mod_cast le_top)).contDiffAt le_rfl, norm_smul,
      Real.norm_of_nonneg hcj] at hle
    exact hle
  have hM : c j * ‖M‖ ≤ ∑ i, ‖b i‖ * C i :=
    calc c j * ‖M‖ ≤ c j * ∑ i, ‖b i‖ * ‖(L i).compContinuousMultilinearMap M‖ :=
          mul_le_mul_of_nonneg_left (norm_le_sum_norm_smulRight_comp b ha M) hcj
      _ = ∑ i, ‖b i‖ * (c j * ‖(L i).compContinuousMultilinearMap M‖) := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i, ‖b i‖ * C i := Finset.sum_le_sum fun i _ => by gcongr; exact hi i
  have hbig := lt_mul_of_inv_pow_le (j := j) (norm_nonneg _) (hτ.id_le j) (hc j) (hx (τ j))
  linarith

/-- **Galbis–Jordá.** Let `φ : D → E` be smooth, with `E` finite-dimensional and `F ≠ 0`. Then
`f ∘ φ` is a Schwartz function for every `f ∈ 𝓢(E, F)` if and only if every derivative of `φ` is
bounded by a power of `1 + ‖φ‖` and `‖x‖` is bounded by a power of `1 + ‖φ x‖`. -/
theorem forall_exists_comp_iff {φ : D → E} (hφ : ContDiff ℝ ∞ φ) :
    (∀ f : 𝓢(E, F), ∃ g : 𝓢(D, F), ∀ x, g x = f (φ x)) ↔
      (∀ n, ∃ (l : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C * (1 + ‖φ x‖) ^ l) ∧
        ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖φ x‖) ^ k :=
  ⟨fun h => ⟨exists_norm_iteratedFDeriv_le_of_forall_exists_comp hφ h,
    exists_norm_le_of_forall_exists_comp h⟩,
    fun ⟨hd, hu⟩ f => ⟨compSymbolCLM ℝ hφ hd hu f, fun _ => rfl⟩⟩

/-- **Composition with a bijection.** Let `e : D ≃ E` with `e` and `e⁻¹` smooth, `D` and `E`
finite-dimensional. Then `f ↦ f ∘ e` maps `𝓢(E, F)` onto `𝓢(D, F)` if and only if `e` and `e⁻¹`
have temperate growth. The Galbis–Jordá conditions for `e` and `e⁻¹` together say no more. -/
theorem forall_exists_comp_equiv_iff [FiniteDimensional ℝ D] (e : D ≃ E)
    (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm) :
    ((∀ f : 𝓢(E, F), ∃ g : 𝓢(D, F), ∀ x, g x = f (e x)) ∧
      ∀ f : 𝓢(D, F), ∃ g : 𝓢(E, F), ∀ y, g y = f (e.symm y)) ↔
      (e : D → E).HasTemperateGrowth ∧ (e.symm : E → D).HasTemperateGrowth := by
  constructor
  · rintro ⟨h, h'⟩
    obtain ⟨hd, k, C, hu⟩ := (forall_exists_comp_iff he).1 h
    obtain ⟨hd', k', C', hu'⟩ := (forall_exists_comp_iff he').1 h'
    exact ⟨hasTemperateGrowth_of_le he hd ⟨k', C', fun x => by simpa using hu' (e x)⟩,
      hasTemperateGrowth_of_le he' hd' ⟨k, C, fun y => by simpa using hu (e.symm y)⟩⟩
  · rintro ⟨hte, hte'⟩
    exact ⟨fun f => ⟨compCLM ℝ hte (exists_norm_le_of_hasTemperateGrowth_symm e hte') f,
      fun _ => rfl⟩, fun f => ⟨compCLM ℝ hte'
        (exists_norm_le_of_hasTemperateGrowth_symm e.symm hte) f, fun _ => rfl⟩⟩

end Necessity

end SchwartzMap
