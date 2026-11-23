/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.FurtherResults.GelfandShilov

/-!
# Further results: Woronowicz's moment condition on `S^{1/2}_{1/2}(ℝ)`

Not part of the brief. This file checks the estimate in the proof of Theorem 5.4 of
`further-results.tex` in the brief's directory (R. Stephan, *Further results on the brief
"Physical vector spaces for quantum mechanics"*): every `ψ ∈ S^{1/2}_{1/2}(ℝ)` satisfies
Woronowicz's condition for uniqueness in the quantum moment problem, for every `t`.

With `a† ψₙ = √(n+1) ψₙ₊₁` and `a ψₙ = √n ψₙ₋₁`, Woronowicz's condition on the state
`ω = ⟨ψ, · ψ⟩` reads `∑ₖ ω(aᵏ (a†)ᵏ)^{1/2} tᵏ / k! < ∞`. Here `ω(aᵏ (a†)ᵏ) = ‖(a†)ᵏ ψ‖²`, and
if the Hermite coefficients of `ψ` decrease exponentially, then `‖(a†)ᵏ ψ‖² ≤ k! S qᵏ`. The
series then converges for every `t`. Woronowicz's theorem itself, that the condition makes the
representing density operator unique, is not formalized.

## Main definitions

* `creationOp`, `annihilationOp`: `a† = a₊/√2` and `a = a₋/√2`.

## Main results

* `creationOp_hermite`: `a† ψₙ = √(n+1) ψₙ₊₁`;
* `inner_annihilationOp_pow_creationOp_pow`: `⟨ψ, aᵏ (a†)ᵏ ψ⟩ = ‖(a†)ᵏ ψ‖²`;
* `hasSum_norm_coef_sq`: `‖f‖² = ∑ₙ |cₙ(f)|²`;
* `norm_coef_creationOp_pow_sq`: `|cₙ((a†)ᵏ f)|² = n (n-1) ⋯ (n-k+1) |cₙ₋ₖ(f)|²`;
* `exists_norm_creationOp_pow_sq_le`: for `ψ ∈ S^{1/2}_{1/2}(ℝ)`, `‖(a†)ᵏ ψ‖² ≤ k! S qᵏ`;
* `summable_woronowicz`: Woronowicz's series converges for every `t`.

## References

* S. L. Woronowicz, The quantum problem of moments I, Rep. Math. Phys. 1 (1970) 135–145,
  Theorem.
-/

open SchwartzMap MeasureTheory Complex Nat
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-- The creation operator `a† = (X - D)/√2`. -/
def creationOp : Module.End ℂ 𝓢(ℝ, ℂ) := ((√2 : ℝ) : ℂ)⁻¹ • raiseOp

/-- The annihilation operator `a = (X + D)/√2`. -/
def annihilationOp : Module.End ℂ 𝓢(ℝ, ℂ) := ((√2 : ℝ) : ℂ)⁻¹ • lowerOp

/-- `a† ψₙ = √(n+1) ψₙ₊₁`. -/
lemma creationOp_hermite (n : ℕ) :
    creationOp (hermite n) = (√((n : ℝ) + 1) : ℂ) • hermite (n + 1) := by
  rw [creationOp, LinearMap.smul_apply, raiseOp_hermite, smul_smul, ← ofReal_inv, ← ofReal_mul,
    Real.sqrt_mul zero_le_two, inv_mul_cancel_left₀ (by positivity)]

/-- `a` is the formal adjoint of `a†`. -/
lemma inner_annihilationOp (f g : 𝓢(ℝ, ℂ)) :
    l2Core.inner f (annihilationOp g) = l2Core.inner (creationOp f) g := by
  have h1 := isSymmetric_posOp f g
  have h2 := l2Core_inner_derivOp f g
  simp only [l2Core_inner_eq] at h1 h2
  simp only [annihilationOp, creationOp, lowerOp, raiseOp, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.sub_apply, l2Core_inner_eq, map_smul, map_add, map_sub,
    inner_smul_left, inner_smul_right, inner_add_right, inner_sub_left, map_inv₀, conj_ofReal]
  rw [h1, h2]
  ring

lemma inner_annihilationOp_pow (k : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    l2Core.inner f ((annihilationOp ^ k) g) = l2Core.inner ((creationOp ^ k) f) g := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [_root_.pow_succ, _root_.pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih,
      inner_annihilationOp]

/-- `⟨ψ, aᵏ (a†)ᵏ ψ⟩ = ‖(a†)ᵏ ψ‖²`. -/
theorem inner_annihilationOp_pow_creationOp_pow (k : ℕ) (ψ : 𝓢(ℝ, ℂ)) :
    l2Core.inner ψ ((annihilationOp ^ k * creationOp ^ k) ψ) =
      ((‖((creationOp ^ k) ψ).toLp 2‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_apply_eq_comp, inner_annihilationOp_pow, l2Core_inner_eq, toLpCLM_apply,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-! ### Hermite coefficients -/

lemma coef_eq_repr (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    coef n f = (TauCeti.hermiteHilbertBasis ℂ).repr (f.toLp 2) n := by
  rw [HilbertBasis.repr_apply_apply, TauCeti.coe_hermiteHilbertBasis]
  rfl

/-- **Parseval**: `‖f‖² = ∑ₙ |cₙ(f)|²`. -/
lemma hasSum_norm_coef_sq (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun n => ‖coef n f‖ ^ 2) (‖f.toLp 2‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) ((TauCeti.hermiteHilbertBasis ℂ).repr (f.toLp 2))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at h
  simpa only [coef_eq_repr] using h

/-- `|cₙ(a† f)|² = n |cₙ₋₁(f)|²`. -/
lemma norm_coef_creationOp_sq (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ‖coef n (creationOp f)‖ ^ 2 = n * ‖coef (n - 1) f‖ ^ 2 := by
  rw [creationOp, LinearMap.smul_apply, coef_smul, coef_raiseOp, norm_mul, norm_mul, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, inv_pow,
    Real.sq_sqrt zero_le_two, Real.sq_sqrt (by positivity)]
  field_simp

/-- `|cₙ((a†)ᵏ f)|² = n (n-1) ⋯ (n-k+1) |cₙ₋ₖ(f)|²`. -/
lemma norm_coef_creationOp_pow_sq (k n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ‖coef n ((creationOp ^ k) f)‖ ^ 2 = n.descFactorial k * ‖coef (n - k) f‖ ^ 2 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' creationOp, mul_apply_eq_comp, norm_coef_creationOp_sq, ih]
    rcases n with _ | m
    · simp
    · rw [Nat.succ_descFactorial_succ, Nat.add_sub_cancel, Nat.add_sub_add_right]
      push_cast
      ring

/-- `C(j+k, j) xʲ yᵏ ≤ 1` for `x, y > 0` with `x + y = 1`. -/
lemma choose_mul_pow_mul_pow_le_one (j k : ℕ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) : ((j + k).choose j : ℝ) * (x ^ j * y ^ k) ≤ 1 := by
  have h := add_pow x y (j + k)
  rw [hxy, one_pow] at h
  rw [h]
  have := Finset.single_le_sum (s := Finset.range (j + k + 1))
    (f := fun m => x ^ m * y ^ (j + k - m) * ((j + k).choose m : ℝ))
    (fun m _ => by positivity) (Finset.mem_range.2 (by omega : j < j + k + 1))
  simp only [Nat.add_sub_cancel_left] at this
  calc ((j + k).choose j : ℝ) * (x ^ j * y ^ k) = x ^ j * y ^ k * (j + k).choose j := by ring
    _ ≤ _ := this

/-- `(j+k)!/j! ≤ k! ρʲ (1 - ρ⁻¹)⁻ᵏ` for `ρ > 1`. -/
lemma descFactorial_le (j k : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ((j + k).descFactorial k : ℝ) ≤ k ! * ρ ^ j * (1 - ρ⁻¹)⁻¹ ^ k := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hy : 0 < 1 - ρ⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hρ)
  have h := choose_mul_pow_mul_pow_le_one j k (inv_pos.2 hρ0) hy (add_sub_cancel _ _)
  rw [← le_div_iff₀ (by positivity), one_div, mul_inv, ← inv_pow, ← inv_pow, inv_inv] at h
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← Nat.choose_symm_add, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ### The moment bound -/

/-- **Moment bound.** For `ψ ∈ S^{1/2}_{1/2}(ℝ)` there are `S ≥ 0` and `q > 0` with
`‖(a†)ᵏ ψ‖² ≤ k! S qᵏ` for all `k`. -/
theorem exists_norm_creationOp_pow_sq_le {ψ : 𝓢(ℝ, ℂ)} (hψ : ψ ∈ gelfandShilov) :
    ∃ S q : ℝ, 0 ≤ S ∧ 0 < q ∧
      ∀ k : ℕ, ‖((creationOp ^ k) ψ).toLp 2‖ ^ 2 ≤ k ! * S * q ^ k := by
  obtain ⟨C, ε, hε, hC⟩ := hψ
  set ρ := Real.exp ε
  have hρ : 1 < ρ := Real.one_lt_exp_iff.2 hε
  have hy : 0 < 1 - ρ⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hρ)
  -- `S = ∑ⱼ ρʲ |cⱼ(ψ)|²`, finite since `ρʲ |cⱼ(ψ)|² ≤ C² e^{-εj}`
  have hS : Summable fun j : ℕ => ρ ^ j * ‖coef j ψ‖ ^ 2 := by
    refine (summable_geometric_of_lt_one (Real.exp_pos (-ε)).le
      (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hε))).mul_left (C ^ 2) |>.of_nonneg_of_le
      (fun j => by positivity) fun j => ?_
    have h2 : ‖coef j ψ‖ ^ 2 ≤ (C * Real.exp (-(ε * j))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hC j) 2
    have he : ρ ^ j * Real.exp (-(ε * j)) ^ 2 = Real.exp (-ε) ^ j := by
      rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_natCast_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    calc ρ ^ j * ‖coef j ψ‖ ^ 2 ≤ ρ ^ j * (C * Real.exp (-(ε * j))) ^ 2 := by gcongr
      _ = C ^ 2 * Real.exp (-ε) ^ j := by rw [mul_pow, ← he]; ring
  refine ⟨∑' j, ρ ^ j * ‖coef j ψ‖ ^ 2, (1 - ρ⁻¹)⁻¹, tsum_nonneg fun j => by positivity,
    by positivity, fun k => ?_⟩
  -- the first `k` coefficients of `(a†)ᵏ ψ` vanish
  have h := hasSum_norm_coef_sq ((creationOp ^ k) ψ)
  simp only [norm_coef_creationOp_pow_sq] at h
  have h0 : ∑ i ∈ Finset.range k, (i.descFactorial k : ℝ) * ‖coef (i - k) ψ‖ ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [(Nat.descFactorial_eq_zero_iff_lt).2 (Finset.mem_range.1 hi), Nat.cast_zero, zero_mul]
  rw [← hasSum_nat_add_iff' k, h0, sub_zero] at h
  simp only [Nat.add_sub_cancel] at h
  refine hasSum_le (fun j => ?_) h (hS.hasSum.mul_left (k ! * (1 - ρ⁻¹)⁻¹ ^ k)) |>.trans_eq
    (by ring)
  calc ((j + k).descFactorial k : ℝ) * ‖coef j ψ‖ ^ 2
      ≤ k ! * ρ ^ j * (1 - ρ⁻¹)⁻¹ ^ k * ‖coef j ψ‖ ^ 2 := by
        gcongr
        exact descFactorial_le j k hρ
    _ = k ! * (1 - ρ⁻¹)⁻¹ ^ k * (ρ ^ j * ‖coef j ψ‖ ^ 2) := by ring

/-- If `Nₖ² ≤ k! S qᵏ`, then `∑ₖ Nₖ tᵏ / k!` converges for every `t`. -/
lemma summable_mul_pow_div_factorial {N : ℕ → ℝ} {S q : ℝ} (hN0 : ∀ k, 0 ≤ N k)
    (hN : ∀ k, N k ^ 2 ≤ k ! * S * q ^ k) (t : ℝ) :
    Summable fun k => N k * t ^ k / k ! := by
  -- `Nₖ |t|ᵏ / k! = 2⁻ᵏ ⬝ (2ᵏ Nₖ |t|ᵏ / k!) ≤ (4⁻ᵏ + S (4 q t²)ᵏ / k!) / 2`
  have hg : Summable fun k : ℕ => ((1 / 4 : ℝ) ^ k + S * ((4 * q * t ^ 2) ^ k / k !)) / 2 :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).add
      ((Real.summable_pow_div_factorial _).mul_left S)).div_const 2
  refine hg.of_norm_bounded fun k => ?_
  have hk : (0 : ℝ) < k ! := by positivity
  set y := (2 * |t|) ^ k * N k / (k ! : ℝ)
  have hy : y ^ 2 ≤ S * ((4 * q * t ^ 2) ^ k / k !) := by
    have h4 : ((2 * |t|) ^ k) ^ 2 = (4 * t ^ 2) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, mul_pow, sq_abs]
      norm_num
    calc y ^ 2 = (4 * t ^ 2) ^ k * N k ^ 2 / (k ! : ℝ) ^ 2 := by
          rw [div_pow, mul_pow, h4]
      _ ≤ (4 * t ^ 2) ^ k * (k ! * S * q ^ k) / (k ! : ℝ) ^ 2 := by gcongr; exact hN k
      _ = S * ((4 * q * t ^ 2) ^ k / k !) := by
          rw [mul_pow, mul_pow]
          field_simp
          ring
  have hxy : N k * |t| ^ k / k ! = (1 / 2 : ℝ) ^ k * y := by
    simp only [y, mul_pow]
    field_simp
    rw [mul_assoc (N k * |t| ^ k), ← mul_pow]
    norm_num
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_nonneg (hN0 k), Nat.abs_cast, hxy]
  have h2 : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  nlinarith [two_mul_le_add_sq ((1 / 2 : ℝ) ^ k) y]

/-- **Woronowicz's condition holds on `S^{1/2}_{1/2}(ℝ)`.** For `ψ ∈ S^{1/2}_{1/2}(ℝ)` and the
state `ω = ⟨ψ, · ψ⟩`, the series `∑ₖ ω(aᵏ (a†)ᵏ)^{1/2} tᵏ / k!` converges for every `t`. -/
theorem summable_woronowicz {ψ : 𝓢(ℝ, ℂ)} (hψ : ψ ∈ gelfandShilov) (t : ℝ) :
    Summable fun k : ℕ =>
      √(l2Core.inner ψ ((annihilationOp ^ k * creationOp ^ k) ψ)).re * t ^ k / k ! := by
  obtain ⟨S, q, -, -, hb⟩ := exists_norm_creationOp_pow_sq_le hψ
  simp only [inner_annihilationOp_pow_creationOp_pow, ofReal_re, Real.sqrt_sq (norm_nonneg _)]
  exact summable_mul_pow_div_factorial (fun _ => norm_nonneg _) hb t

end QuantumVectorSpaces.FurtherResults
