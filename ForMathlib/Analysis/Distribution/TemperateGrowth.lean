/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# More functions of temperate growth

## Main results

* `Function.HasTemperateGrowth.fderiv`: the derivative of a function of temperate growth has
  temperate growth;
* `Function.HasTemperateGrowth.prod`: so does a finite product of such functions;
* `Function.HasTemperateGrowth.rpow`: if `h > 0` has temperate growth and `1 / h` is polynomially
  bounded, then `h ^ r` has temperate growth for every real `r`;
* `Function.HasTemperateGrowth.det_fderiv`: the Jacobian determinant of a map of temperate growth
  of a finite-dimensional space has temperate growth.
-/

@[expose] public section

open scoped Nat ContDiff

namespace Function

variable {ι E F R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a function of temperate growth has temperate growth. -/
theorem HasTemperateGrowth.fderiv {f : E → F} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right le_rfl, fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

/-- A finite product of functions of temperate growth has temperate growth. -/
theorem HasTemperateGrowth.prod [NormedCommRing R] [NormedAlgebra ℝ R] {f : ι → E → R}
    {s : Finset ι} (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- For `y > 0` and `|s| ≤ m`, `y ^ s ≤ max y y⁻¹ ^ m`. -/
private lemma rpow_le_max_inv_pow {y s : ℝ} (hy : 0 < y) {m : ℕ} (hm : |s| ≤ m) :
    y ^ s ≤ max y y⁻¹ ^ m := by
  rw [← Real.rpow_natCast]
  rcases le_total 1 y with h | h
  · calc y ^ s ≤ y ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h ((le_abs_self s).trans hm)
      _ ≤ max y y⁻¹ ^ (m : ℝ) := Real.rpow_le_rpow hy.le (le_max_left _ _) (by positivity)
  · have h' : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.2 h
    calc y ^ s = y⁻¹ ^ (-s) := by rw [Real.inv_rpow hy.le, Real.rpow_neg hy.le, inv_inv]
      _ ≤ y⁻¹ ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h' ((neg_le_abs s).trans hm)
      _ ≤ max y y⁻¹ ^ (m : ℝ) := Real.rpow_le_rpow (by positivity) (le_max_right _ _)
          (by positivity)

/-- **Real powers of a function of temperate growth.** If `h > 0` has temperate growth and `1 / h`
is polynomially bounded, then `h ^ r` has temperate growth for every real `r`. -/
theorem HasTemperateGrowth.rpow {h : E → ℝ} (hh : h.HasTemperateGrowth) (hpos : ∀ x, 0 < h x)
    (hlow : ∃ (k : ℕ) (C : ℝ), ∀ x, (h x)⁻¹ ≤ C * (1 + ‖x‖) ^ k) (r : ℝ) :
    (fun x => h x ^ r).HasTemperateGrowth := by
  set t := Set.Ioi (0 : ℝ)
  have ht : Set.range h ⊆ t := by rintro - ⟨x, rfl⟩; exact hpos x
  have hunique : UniqueDiffOn ℝ t := isOpen_Ioi.uniqueDiffOn
  have hdiff : ContDiffOn ℝ ∞ (fun y : ℝ => y ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun y hy => (ne_of_gt hy)
  refine ⟨hdiff.comp_contDiff hh.1 (ht ⟨·, rfl⟩), fun n => ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hh.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, h₂⟩ := hlow
  obtain ⟨m, hm⟩ := exists_nat_ge (|r| + n)
  set P := ∑ i ∈ Finset.range (n + 1), ‖Polynomial.eval r (descPochhammer ℝ i)‖
  set A := 1 + C₁ + |C₂|
  have hA : 1 ≤ A := by simp only [A]; linarith [abs_nonneg C₂]
  have hP : 0 ≤ P := by positivity
  refine ⟨(k₁ + k₂) * m + k₁ * n, n ! * (P * A ^ m) * (1 + C₁) ^ n, fun x => ?_⟩
  have hx1 : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
  have hpow : ∀ j : ℕ, 1 ≤ (1 + ‖x‖) ^ j := fun j => one_le_pow₀ hx1
  have hup : h x ≤ C₁ * (1 + ‖x‖) ^ k₁ :=
    (le_abs_self _).trans (by simpa using h₁ 0 (Nat.zero_le n) x)
  have hmax : max (h x) (h x)⁻¹ ≤ A * (1 + ‖x‖) ^ (k₁ + k₂) := by
    rw [pow_add]
    refine max_le ?_ ?_
    · calc h x ≤ C₁ * (1 + ‖x‖) ^ k₁ := hup
        _ ≤ A * (1 + ‖x‖) ^ k₁ * 1 := by
          rw [mul_one]; gcongr; simp only [A]; linarith [abs_nonneg C₂]
        _ ≤ A * (1 + ‖x‖) ^ k₁ * (1 + ‖x‖) ^ k₂ := by gcongr; exact hpow k₂
        _ = _ := by ring
    · calc (h x)⁻¹ ≤ C₂ * (1 + ‖x‖) ^ k₂ := h₂ x
        _ ≤ A * (1 + ‖x‖) ^ k₂ * 1 := by
          rw [mul_one]; gcongr; simp only [A]; linarith [le_abs_self C₂]
        _ ≤ A * (1 + ‖x‖) ^ k₂ * (1 + ‖x‖) ^ k₁ := by gcongr; exact hpow k₁
        _ = _ := by ring
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => y ^ r) t (h x)‖ ≤
        P * A ^ m * (1 + ‖x‖) ^ ((k₁ + k₂) * m) := by
    intro i hi
    have hx := hpos x
    have : ContDiffAt ℝ i (fun y : ℝ => y ^ r) (h x) :=
      Real.contDiffAt_rpow_const (Or.inl hx.ne')
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
      Real.iter_deriv_rpow_const, norm_mul, mul_assoc]
    gcongr
    · exact Finset.single_le_sum (f := fun i => ‖Polynomial.eval r (descPochhammer ℝ i)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le _), pow_mul, ← mul_pow]
      have hs : |r - i| ≤ m := by
        calc |r - i| ≤ |r| + |(i : ℝ)| := abs_sub _ _
          _ ≤ |r| + n := by rw [Nat.abs_cast]; gcongr
          _ ≤ m := hm
      exact (rpow_le_max_inv_pow hx hs).trans (pow_le_pow_left₀ (by positivity) hmax m)
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i h x‖ ≤ ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
    intro i hi hi'
    calc _ ≤ C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hi' x
      _ ≤ (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
      _ ≤ _ := le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁]) (hpow k₁)) (by omega)
  calc ‖iteratedFDeriv ℝ n (fun x => h x ^ r) x‖
      ≤ n ! * (P * A ^ m * (1 + ‖x‖) ^ ((k₁ + k₂) * m)) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n :=
        norm_iteratedFDeriv_comp_le' (g := fun y : ℝ => y ^ r) ht hunique hdiff hh.1
          (mod_cast le_top) x hC hD
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- The Jacobian determinant of a map of temperate growth of a finite-dimensional space has
temperate growth. -/
theorem HasTemperateGrowth.det_fderiv [FiniteDimensional ℝ E] {f : E → E}
    (hf : f.HasTemperateGrowth) :
    (fun x => LinearMap.det (_root_.fderiv ℝ f x : E →ₗ[ℝ] E)).HasTemperateGrowth := by
  classical
  let b := Module.finBasis ℝ E
  have hentry : ∀ i j, (fun x => LinearMap.toMatrix b b (_root_.fderiv ℝ f x : E →ₗ[ℝ] E) i j)
      |>.HasTemperateGrowth := by
    intro i j
    let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap (b.coord i) ∘L ContinuousLinearMap.apply ℝ E (b j)
    have := L.hasTemperateGrowth.comp hf.fderiv
    convert this using 1
    ext x
    simp [L, LinearMap.toMatrix_apply]
  have : (fun x => LinearMap.det (_root_.fderiv ℝ f x : E →ₗ[ℝ] E)) = fun x =>
      ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, LinearMap.toMatrix b b (_root_.fderiv ℝ f x : E →ₗ[ℝ] E) (σ i) i := by
    ext x
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [Units.smul_def, zsmul_eq_mul]
  rw [this]
  exact HasTemperateGrowth.sum fun σ _ =>
    (HasTemperateGrowth.const _).mul (HasTemperateGrowth.prod fun i _ => hentry (σ i) i)

end Function
