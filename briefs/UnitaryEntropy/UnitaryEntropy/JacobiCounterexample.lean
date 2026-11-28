/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.ForwardHamiltonian

/-!
# Without bounded differences an invariant core is not enough: a Jacobi-matrix evolution

`QuantumMechanics.isEssentiallySelfAdjoint_forwardHamiltonian` asks for a dense subspace `D`,
invariant under every `F t`, on which the orbits are differentiable, and on which the generators
near `0` differ from the one at `0` by bounded operators. The last condition cannot be dropped.

On `ℓ²(ℕ)` let `A` act on the pairs `(e_{2k}, e_{2k+1})` by `4ᵏ σₓ`, and `B` on the pairs
`(e_{2k+1}, e_{2k+2})` by `2 · 4ᵏ σₓ` (and by `0` on `e₀`). Both are direct sums of `2 × 2`
matrices, so `e^{-iτA}` and `e^{-iτB}` are explicit rotations on each pair. Let `D` be the
finitely supported sequences and
`U(t, s) = e^{-itB} e^{-i(t-s)A} e^{isB}`, a unitary propagator, with `F τ = U(τ, 0)`.
`D` is dense and invariant, and every orbit `τ ↦ F τ x`, `x ∈ D`, stays in a finite-dimensional
subspace. On `D` the forward Hamiltonian is `ħ J`, where `J = A + B` is the Jacobi matrix with
zero diagonal and off-diagonal entries `cₙ = 2ⁿ`.

`J` restricted to `D` is not essentially self-adjoint. The sequences
`u = (1, 0, -1/2, 0, 1/4, …)` and `v = (0, 1, 0, -1/2, 0, 1/4, …)` are square summable, with
`J u = 0` and `J v = e₀` row by row. Against finitely supported `x` the sums are finite, so `u`
and `v` lie in the domain of the adjoint, and `⟨J* u, v⟩ - ⟨u, J* v⟩ = -1`. The adjoint of an
essentially self-adjoint operator is symmetric. This is the indeterminate case of a Jacobi
matrix: `∑ 1/cₙ < ∞`.

## Main results

* `Pairing.rotU`: the rotation `e^{-iτK}` of a pairing, unitary, with `rotU (s + t) =
  rotU s * rotU t`.
* `jacobiPropagator`: `U(t, s)`, unitary, `U(t, t) = 1`, `U(t, r) U(r, s) = U(t, s)`.
* `forwardHamiltonian_jacobi`: on `D`, the forward Hamiltonian of `F τ = U(τ, 0)` is `ħ J`.
* `not_isEssentiallySelfAdjoint_jacobi`: its restriction to `D` is not essentially self-adjoint.
* `jacobi_counterexample`: all hypotheses of
  `QuantumMechanics.isEssentiallySelfAdjoint_forwardHamiltonian` except the bounded differences
  hold, and the conclusion fails.
* `not_boundedDifference_jacobi`: hence the bounded-difference condition fails.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open Filter Topology Set QuantumMechanics
open scoped InnerProductSpace ComplexConjugate LinearPMap

/-- `ℓ²(ℕ)`. -/
local notation "ℓ²ℕ" => lp (fun _ : ℕ => ℂ) 2

/-- A pairing of the indices: an involution `ptn` that moves each index by at most one, with a
real coefficient `κ` constant on each pair. It defines the operator `(K x)ₙ = κₙ x_{ptn n}`, a
direct sum of `κ σₓ` on the pairs and of `κ` on the fixed points. -/
structure Pairing where
  /-- The partner of an index. -/
  ptn : ℕ → ℕ
  /-- The coefficient of a pair. -/
  κ : ℕ → ℝ
  ptn_ptn : ∀ n, ptn (ptn n) = n
  κ_ptn : ∀ n, κ (ptn n) = κ n
  le_ptn : ∀ n, n ≤ ptn n + 1

namespace Pairing

variable (P : Pairing)

/-- `e^{-iτK}` on sequences: `cos(κτ) - i sin(κτ) σₓ` on each pair. -/
def rot (τ : ℝ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  Real.cos (P.κ n * τ) * x n - Complex.I * Real.sin (P.κ n * τ) * x (P.ptn n)

/-- The generator `(K x)ₙ = κₙ x_{ptn n}`. -/
def gen (x : ℕ → ℂ) (n : ℕ) : ℂ := P.κ n * x (P.ptn n)

lemma rot_ptn (τ : ℝ) (x : ℕ → ℂ) (n : ℕ) :
    P.rot τ x (P.ptn n) =
      Real.cos (P.κ n * τ) * x (P.ptn n) - Complex.I * Real.sin (P.κ n * τ) * x n := by
  simp [rot, P.κ_ptn, P.ptn_ptn]

lemma rot_zero (x : ℕ → ℂ) : P.rot 0 x = x := by
  ext n
  simp [rot]

lemma rot_rot (s t : ℝ) (x : ℕ → ℂ) : P.rot s (P.rot t x) = P.rot (s + t) x := by
  ext n
  simp only [rot, P.κ_ptn, P.ptn_ptn, mul_add, Real.cos_add, Real.sin_add, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (Real.sin (P.κ n * s) * Real.sin (P.κ n * t) * x n : ℂ) * Complex.I_sq

lemma norm_sq_add_norm_sq (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (a b : ℂ) :
    ‖(c : ℂ) * a - Complex.I * s * b‖ ^ 2 + ‖(c : ℂ) * b - Complex.I * s * a‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  linear_combination (a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2) * h

lemma norm_rot_sq_add (τ : ℝ) (x : ℕ → ℂ) (n : ℕ) :
    ‖P.rot τ x n‖ ^ 2 + ‖P.rot τ x (P.ptn n)‖ ^ 2 = ‖x n‖ ^ 2 + ‖x (P.ptn n)‖ ^ 2 := by
  rw [rot_ptn]
  exact norm_sq_add_norm_sq _ _ (Real.cos_sq_add_sin_sq _) _ _

/-- `ptn` as a permutation. -/
def perm : Equiv.Perm ℕ := Function.Involutive.toPerm P.ptn P.ptn_ptn

@[simp] lemma perm_apply (n : ℕ) : P.perm n = P.ptn n := rfl

/-- Pair sums: if `f + f ∘ ptn = g + g ∘ ptn` with `f, g ≥ 0` and `g` summable, then `f` is
summable with the same sum. -/
lemma summable_and_tsum_eq {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hg : Summable g)
    (h : ∀ n, f n + f (P.ptn n) = g n + g (P.ptn n)) : Summable f ∧ ∑' n, f n = ∑' n, g n := by
  have hgσ : Summable fun n => g (P.ptn n) := P.perm.summable_iff.mpr hg
  have hfs : Summable f := (hg.add hgσ).of_nonneg_of_le hf fun n => by
    have := hf (P.ptn n)
    linarith [h n]
  have hfσ : Summable fun n => f (P.ptn n) := P.perm.summable_iff.mpr hfs
  refine ⟨hfs, ?_⟩
  have e1 : ∑' n, f (P.ptn n) = ∑' n, f n := P.perm.tsum_eq f
  have e2 : ∑' n, g (P.ptn n) = ∑' n, g n := P.perm.tsum_eq g
  have : ∑' n, (f n + f (P.ptn n)) = ∑' n, (g n + g (P.ptn n)) := tsum_congr h
  rw [hfs.tsum_add hfσ, hg.tsum_add hgσ, e1, e2] at this
  linarith

lemma hasSum_rot (τ : ℝ) (x : ℓ²ℕ) :
    Summable (fun n => ‖P.rot τ x n‖ ^ 2) ∧
      ∑' n, ‖P.rot τ x n‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  have hx : Summable fun n => ‖x n‖ ^ 2 := by
    simpa using (lp.hasSum_norm (p := 2) (by norm_num) x).summable
  exact P.summable_and_tsum_eq (fun n => by positivity) hx (P.norm_rot_sq_add τ x)

lemma memℓp_rot (τ : ℝ) (x : ℓ²ℕ) : Memℓp (P.rot τ x) 2 :=
  memℓp_gen (by simpa using (P.hasSum_rot τ x).1)

lemma norm_rot (τ : ℝ) (x : ℓ²ℕ) : ‖(⟨P.rot τ x, P.memℓp_rot τ x⟩ : ℓ²ℕ)‖ = ‖x‖ := by
  have h1 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (⟨P.rot τ x, P.memℓp_rot τ x⟩ : ℓ²ℕ)
  have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2
  have h : ‖(⟨P.rot τ x, P.memℓp_rot τ x⟩ : ℓ²ℕ)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [h1, h2]
    exact (P.hasSum_rot τ x).2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- `e^{-iτK}` as a linear isometry equivalence of `ℓ²(ℕ)`. -/
def rotL (τ : ℝ) : ℓ²ℕ ≃ₗᵢ[ℂ] ℓ²ℕ where
  toFun x := ⟨P.rot τ x, P.memℓp_rot τ x⟩
  map_add' x y := lp.ext <| by
    ext n
    simp only [rot, lp.coeFn_add, Pi.add_apply]
    show _ = P.rot τ x n + P.rot τ y n
    simp only [rot]
    ring
  map_smul' c x := lp.ext <| by
    ext n
    simp only [rot, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    show _ = c * P.rot τ x n
    simp only [rot]
    ring
  invFun x := ⟨P.rot (-τ) x, P.memℓp_rot (-τ) x⟩
  left_inv x := lp.ext <| by
    show P.rot (-τ) (P.rot τ x) = x
    rw [rot_rot, neg_add_cancel, rot_zero]
  right_inv x := lp.ext <| by
    show P.rot τ (P.rot (-τ) x) = x
    rw [rot_rot, add_neg_cancel, rot_zero]
  norm_map' := P.norm_rot τ

/-- `e^{-iτK}` as a continuous linear map. -/
def rotU (τ : ℝ) : ℓ²ℕ →L[ℂ] ℓ²ℕ := ((P.rotL τ : ℓ²ℕ ≃L[ℂ] ℓ²ℕ) : ℓ²ℕ →L[ℂ] ℓ²ℕ)

@[simp] lemma rotU_apply (τ : ℝ) (x : ℓ²ℕ) (n : ℕ) : P.rotU τ x n = P.rot τ x n := rfl

lemma rotU_mem_unitary (τ : ℝ) : P.rotU τ ∈ unitary (ℓ²ℕ →L[ℂ] ℓ²ℕ) :=
  (Unitary.linearIsometryEquiv.symm (P.rotL τ)).property

lemma rotU_zero : P.rotU 0 = 1 := by
  ext1 x
  exact lp.ext (P.rot_zero x)

lemma rotU_add (s t : ℝ) : P.rotU (s + t) = P.rotU s * P.rotU t := by
  ext1 x
  exact lp.ext (P.rot_rot s t x).symm

end Pairing

/-! ### Finitely supported sequences -/

/-- The finitely supported sequences in `ℓ²(ℕ)`. -/
def finSupp : Submodule ℂ ℓ²ℕ where
  carrier := {x | ∃ N, ∀ n, N ≤ n → x n = 0}
  add_mem' := by
    rintro x y ⟨N, hN⟩ ⟨M, hM⟩
    exact ⟨max N M, fun n hn => by
      simp [hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩
  zero_mem' := ⟨0, fun n _ => rfl⟩
  smul_mem' := by
    rintro c x ⟨N, hN⟩
    exact ⟨N, fun n hn => by simp [hN n hn]⟩

lemma mem_finSupp {x : ℓ²ℕ} : x ∈ finSupp ↔ ∃ N, ∀ n, N ≤ n → x n = 0 := Iff.rfl

lemma dense_finSupp : Dense (finSupp : Set ℓ²ℕ) := by
  intro x
  have h := (lp.hasSum_single (p := 2) ENNReal.ofNat_ne_top x).tendsto_sum_nat
  refine mem_closure_of_tendsto h (Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩)
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  refine Finset.sum_eq_zero fun i hi => ?_
  have : i ≠ n := by
    have := Finset.mem_range.mp hi
    omega
  simp [this.symm]

lemma Pairing.rot_eq_zero (P : Pairing) {x : ℕ → ℂ} {N : ℕ} (hx : ∀ n, N ≤ n → x n = 0)
    (τ : ℝ) (n : ℕ) (hn : N + 1 ≤ n) : P.rot τ x n = 0 := by
  have h1 := P.le_ptn n
  simp [Pairing.rot, hx n (by omega), hx (P.ptn n) (by omega)]

lemma Pairing.rotU_mem_finSupp (P : Pairing) (τ : ℝ) {x : ℓ²ℕ} (hx : x ∈ finSupp) :
    P.rotU τ x ∈ finSupp := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨N + 1, fun n hn => P.rot_eq_zero hN τ n hn⟩

/-! ### Coordinates and derivatives in `ℓ²(ℕ)` -/

/-- A vector supported in `[0, M)` is the sum of its coordinates. -/
lemma eq_sum_single {y : ℓ²ℕ} {M : ℕ} (h : ∀ n, M ≤ n → y n = 0) :
    y = ∑ n ∈ Finset.range M, lp.single 2 n (y n) := by
  refine lp.ext (funext fun m => ?_)
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hm
  · rfl
  · exact h m (by simpa using hm)

lemma memℓp_of_eq_zero {f : ℕ → ℂ} {M : ℕ} (h : ∀ n, M ≤ n → f n = 0) : Memℓp f 2 :=
  memℓp_gen (summable_of_ne_finset_zero (s := Finset.range M) fun n hn => by
    simp [h n (by simpa using hn)])

/-- A path in `ℓ²(ℕ)` supported in a fixed `[0, M)` has the derivative of its coordinates. -/
lemma hasDerivAt_of_coord {y : ℝ → ℓ²ℕ} {y' : ℓ²ℕ} {M : ℕ} {t : ℝ}
    (hy : ∀ s n, M ≤ n → y s n = 0) (hy' : ∀ n, M ≤ n → y' n = 0)
    (hd : ∀ n, HasDerivAt (fun s => y s n) (y' n) t) : HasDerivAt y y' t := by
  have e : y = fun s => ∑ n ∈ Finset.range M,
      lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n (y s n) :=
    funext fun s => eq_sum_single (hy s)
  rw [e, eq_sum_single hy']
  exact HasDerivAt.fun_sum fun n _ =>
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivAt t (hd n)

/-- A path in `ℓ²(ℕ)` supported in a fixed `[0, M)` with differentiable coordinates is
differentiable. -/
lemma differentiable_of_coord {y : ℝ → ℓ²ℕ} {M : ℕ} (hy : ∀ s n, M ≤ n → y s n = 0)
    (hd : ∀ n, Differentiable ℝ fun s => y s n) : Differentiable ℝ y := by
  have e : y = fun s => ∑ n ∈ Finset.range M,
      lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n (y s n) :=
    funext fun s => eq_sum_single (hy s)
  rw [e]
  exact Differentiable.fun_sum fun n _ =>
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n).restrictScalars ℝ).differentiable
      |>.comp (hd n)

namespace Pairing

variable (P : Pairing)

lemma hasDerivAt_rot {z : ℝ → ℕ → ℂ} {z' : ℕ → ℂ} {t : ℝ} (n : ℕ)
    (h1 : HasDerivAt (fun s => z s n) (z' n) t)
    (h2 : HasDerivAt (fun s => z s (P.ptn n)) (z' (P.ptn n)) t) :
    HasDerivAt (fun s => P.rot s (z s) n)
      (Real.cos (P.κ n * t) * z' n - Complex.I * Real.sin (P.κ n * t) * z' (P.ptn n)
        - Complex.I * P.κ n * P.rot t (z t) (P.ptn n)) t := by
  have hlin : HasDerivAt (fun s => P.κ n * s) (P.κ n) t := by
    simpa using (hasDerivAt_id t).const_mul (P.κ n)
  have hc := hlin.cos.ofReal_comp
  have hs := hlin.sin.ofReal_comp
  have := (hc.mul h1).sub ((hs.const_mul Complex.I).mul h2)
  convert this using 1
  · ext s
    simp only [rot, Pi.mul_apply, Pi.sub_apply]
  · rw [rot_ptn]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    linear_combination (P.κ n * Real.sin (P.κ n * t) * z t n : ℂ) * Complex.I_sq

lemma hasDerivAt_rot_const (x : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => P.rot s x n) (-(Complex.I * P.κ n * P.rot t x (P.ptn n))) t := by
  have := P.hasDerivAt_rot (z := fun _ => x) (z' := fun _ => 0) (t := t) n
    (hasDerivAt_const _ _) (hasDerivAt_const _ _)
  simpa using this

lemma gen_eq_zero {x : ℕ → ℂ} {N : ℕ} (hx : ∀ n, N ≤ n → x n = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    P.gen x n = 0 := by
  have h1 := P.le_ptn n
  simp [gen, hx (P.ptn n) (by omega)]

/-- `K` is symmetric against sequences of finite support, with no summability: reindex by the
involution. -/
lemma tsum_gen_mul_conj (u x : ℕ → ℂ) :
    ∑' n, P.gen x n * conj (u n) = ∑' n, x n * conj (P.gen u n) := by
  rw [← P.perm.tsum_eq (fun n => P.gen x n * conj (u n))]
  refine tsum_congr fun n => ?_
  simp only [perm_apply, gen, P.ptn_ptn, P.κ_ptn, map_mul, Complex.conj_ofReal]
  ring

end Pairing

/-! ### The Jacobi matrix with `cₙ = 2ⁿ` -/

/-- The partner in `A`: `2k ↔ 2k+1`. -/
def ptnA (n : ℕ) : ℕ := if n % 2 = 0 then n + 1 else n - 1

/-- The coefficient of `A` on the pair `(2k, 2k+1)`: `4ᵏ`. -/
def κA (n : ℕ) : ℝ := 4 ^ (n / 2)

/-- The partner in `B`: `2k+1 ↔ 2k+2`, and `0 ↔ 0`. -/
def ptnB (n : ℕ) : ℕ := if n = 0 then 0 else if n % 2 = 1 then n + 1 else n - 1

/-- The coefficient of `B` on the pair `(2k+1, 2k+2)`: `2 · 4ᵏ`; `0` on the index `0`. -/
def κB (n : ℕ) : ℝ := if n = 0 then 0 else 2 * 4 ^ ((n - 1) / 2)

/-- `A`: the pairs `(2k, 2k+1)`, coefficient `4ᵏ`. -/
def pairA : Pairing where
  ptn := ptnA
  κ := κA
  ptn_ptn n := by unfold ptnA; split_ifs <;> omega
  κ_ptn n := by
    unfold κA
    congr 1
    unfold ptnA
    split_ifs <;> omega
  le_ptn n := by unfold ptnA; split_ifs <;> omega

/-- `B`: the pairs `(2k+1, 2k+2)`, coefficient `2 · 4ᵏ`, and `0` on the index `0`. -/
def pairB : Pairing where
  ptn := ptnB
  κ := κB
  ptn_ptn n := by unfold ptnB; split_ifs <;> first | omega | contradiction
  κ_ptn n := by
    unfold κB ptnB
    by_cases h0 : n = 0
    · simp [h0]
    · by_cases h1 : n % 2 = 1
      · have h2 : n + 1 ≠ 0 := by omega
        simp only [h0, h1, h2, ↓reduceIte]
        congr 2
        omega
      · have h2 : n - 1 ≠ 0 := by omega
        simp only [h0, h1, h2, ↓reduceIte]
        congr 2
        omega
  le_ptn n := by unfold ptnB; split_ifs <;> first | omega

/-- The Jacobi matrix `J = A + B`: zero diagonal, `J_{n,n+1} = J_{n+1,n} = 2ⁿ`. -/
def jac (x : ℕ → ℂ) (n : ℕ) : ℂ := pairA.gen x n + pairB.gen x n

lemma jac_eq_zero {x : ℕ → ℂ} {N : ℕ} (hx : ∀ n, N ≤ n → x n = 0) (n : ℕ) (hn : N + 1 ≤ n) :
    jac x n = 0 := by
  simp [jac, pairA.gen_eq_zero hx n hn, pairB.gen_eq_zero hx n hn]

/-- `J x` for finitely supported `x`, in `ℓ²(ℕ)`. -/
def jacLp {x : ℓ²ℕ} (hx : x ∈ finSupp) : ℓ²ℕ :=
  ⟨jac x, memℓp_of_eq_zero (jac_eq_zero hx.choose_spec)⟩

@[simp] lemma jacLp_apply {x : ℓ²ℕ} (hx : x ∈ finSupp) (n : ℕ) : jacLp hx n = jac x n := rfl

/-- `F τ = e^{-iτB} e^{-iτA}`. -/
def jacobiEvolution (τ : ℝ) : ℓ²ℕ →L[ℂ] ℓ²ℕ := pairB.rotU τ * pairA.rotU τ

/-- The propagator `U(t, s) = e^{-itB} e^{-i(t-s)A} e^{isB}`. -/
def jacobiPropagator (t s : ℝ) : ℓ²ℕ →L[ℂ] ℓ²ℕ :=
  pairB.rotU t * pairA.rotU (t - s) * pairB.rotU (-s)

lemma jacobiPropagator_mem_unitary (t s : ℝ) :
    jacobiPropagator t s ∈ unitary (ℓ²ℕ →L[ℂ] ℓ²ℕ) :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ (pairB.rotU_mem_unitary t)
    (pairA.rotU_mem_unitary _)) (pairB.rotU_mem_unitary _)

lemma jacobiPropagator_self (t : ℝ) : jacobiPropagator t t = 1 := by
  rw [jacobiPropagator, sub_self, pairA.rotU_zero, mul_one, ← pairB.rotU_add, add_neg_cancel,
    pairB.rotU_zero]

lemma jacobiPropagator_mul (t r s : ℝ) :
    jacobiPropagator t r * jacobiPropagator r s = jacobiPropagator t s := by
  simp only [jacobiPropagator, mul_assoc]
  rw [← mul_assoc (pairB.rotU (-r)), ← pairB.rotU_add, neg_add_cancel, pairB.rotU_zero, one_mul,
    ← mul_assoc (pairA.rotU (t - r)), ← pairA.rotU_add, sub_add_sub_cancel]

lemma jacobiEvolution_eq (τ : ℝ) : jacobiEvolution τ = jacobiPropagator τ 0 := by
  simp [jacobiEvolution, jacobiPropagator, pairB.rotU_zero]

lemma jacobiEvolution_zero : jacobiEvolution 0 = 1 := by
  rw [jacobiEvolution_eq, jacobiPropagator_self]

lemma jacobiEvolution_mem_unitary (τ : ℝ) : jacobiEvolution τ ∈ unitary (ℓ²ℕ →L[ℂ] ℓ²ℕ) := by
  rw [jacobiEvolution_eq]
  exact jacobiPropagator_mem_unitary τ 0

lemma jacobiEvolution_apply (τ : ℝ) (x : ℓ²ℕ) (n : ℕ) :
    jacobiEvolution τ x n = pairB.rot τ (pairA.rot τ x) n := rfl

lemma jacobiEvolution_mem_finSupp (τ : ℝ) {x : ℓ²ℕ} (hx : x ∈ finSupp) :
    jacobiEvolution τ x ∈ finSupp :=
  pairB.rotU_mem_finSupp τ (pairA.rotU_mem_finSupp τ hx)

lemma jacobiEvolution_eq_zero {x : ℓ²ℕ} {N : ℕ} (hx : ∀ n, N ≤ n → x n = 0) (τ : ℝ) (n : ℕ)
    (hn : N + 2 ≤ n) : jacobiEvolution τ x n = 0 :=
  pairB.rot_eq_zero (pairA.rot_eq_zero hx τ) τ n (by omega)

lemma hasDerivAt_jacobiEvolution_coord (x : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    HasDerivAt (fun s => pairB.rot s (pairA.rot s x) n)
      (Real.cos (pairB.κ n * t) * -(Complex.I * pairA.κ n * pairA.rot t x (pairA.ptn n))
        - Complex.I * Real.sin (pairB.κ n * t) *
          -(Complex.I * pairA.κ (pairB.ptn n) * pairA.rot t x (pairA.ptn (pairB.ptn n)))
        - Complex.I * pairB.κ n * pairB.rot t (pairA.rot t x) (pairB.ptn n)) t :=
  pairB.hasDerivAt_rot (z := fun s => pairA.rot s x)
    (z' := fun m => -(Complex.I * pairA.κ m * pairA.rot t x (pairA.ptn m))) n
    (pairA.hasDerivAt_rot_const x t n) (pairA.hasDerivAt_rot_const x t _)

lemma differentiable_jacobiEvolution {x : ℓ²ℕ} (hx : x ∈ finSupp) :
    Differentiable ℝ fun τ => jacobiEvolution τ x := by
  obtain ⟨N, hN⟩ := hx
  exact differentiable_of_coord (M := N + 2) (fun s n hn => jacobiEvolution_eq_zero hN s n hn)
    fun n t => (hasDerivAt_jacobiEvolution_coord x t n).differentiableAt

lemma hasDerivAt_jacobiEvolution {x : ℓ²ℕ} (hx : x ∈ finSupp) :
    HasDerivAt (fun τ => jacobiEvolution τ x) (-Complex.I • jacLp hx) 0 := by
  obtain ⟨N, hN⟩ := id hx
  refine hasDerivAt_of_coord (M := N + 2) (fun s n hn => jacobiEvolution_eq_zero hN s n hn)
    (fun n hn => ?_) fun n => ?_
  · rw [lp.coeFn_smul, Pi.smul_apply, jacLp_apply, jac_eq_zero hN n (by omega), smul_zero]
  · refine (hasDerivAt_jacobiEvolution_coord x 0 n).congr_deriv ?_
    rw [lp.coeFn_smul, Pi.smul_apply, jacLp_apply]
    simp only [jac, Pairing.gen, pairA.rot_zero, pairB.rot_zero, mul_zero, Real.cos_zero,
      Real.sin_zero, Complex.ofReal_zero, Complex.ofReal_one, smul_eq_mul]
    ring

/-- **On `D` the forward Hamiltonian is `ħ J`.** -/
theorem forwardHamiltonian_jacobi (ħ : ℝ) {x : ℓ²ℕ} (hx : x ∈ finSupp) :
    ∃ hd : x ∈ forwardDomain jacobiEvolution,
      forwardHamiltonian jacobiEvolution ħ ⟨x, hd⟩ = (ħ : ℂ) • jacLp hx := by
  obtain ⟨hd, h⟩ := forwardHamiltonian_of_hasDerivWithinAt ħ
    (hasDerivAt_jacobiEvolution hx).hasDerivWithinAt
  refine ⟨hd, h.trans ?_⟩
  rw [smul_smul]
  congr 1
  linear_combination (-(ħ : ℂ)) * Complex.I_sq

/-! ### Two vectors in the adjoint domain -/

@[simp] lemma pairA_ptn : pairA.ptn = ptnA := rfl
@[simp] lemma pairA_κ : pairA.κ = κA := rfl
@[simp] lemma pairB_ptn : pairB.ptn = ptnB := rfl
@[simp] lemma pairB_κ : pairB.κ = κB := rfl

lemma ptnA_even (k : ℕ) : ptnA (2 * k) = 2 * k + 1 := by unfold ptnA; split_ifs <;> omega
lemma ptnA_odd (k : ℕ) : ptnA (2 * k + 1) = 2 * k := by unfold ptnA; split_ifs <;> omega
lemma κA_even (k : ℕ) : κA (2 * k) = 4 ^ k := by unfold κA; congr 1; omega
lemma κA_odd (k : ℕ) : κA (2 * k + 1) = 4 ^ k := by unfold κA; congr 1; omega
lemma ptnB_zero : ptnB 0 = 0 := rfl
lemma κB_zero : κB 0 = 0 := rfl
lemma ptnB_odd (k : ℕ) : ptnB (2 * k + 1) = 2 * (k + 1) := by
  unfold ptnB; split_ifs <;> first | omega
lemma ptnB_even (k : ℕ) : ptnB (2 * (k + 1)) = 2 * k + 1 := by
  unfold ptnB; split_ifs <;> first | omega
lemma κB_odd (k : ℕ) : κB (2 * k + 1) = 2 * 4 ^ k := by
  unfold κB; rw [ite_eq_right (by omega)]; congr 2; omega
lemma κB_even (k : ℕ) : κB (2 * (k + 1)) = 2 * 4 ^ k := by
  unfold κB; rw [ite_eq_right (by omega)]; congr 2; omega


/-- `u = (1, 0, -1/2, 0, 1/4, …)`. -/
def uSeq (n : ℕ) : ℂ := if n % 2 = 0 then (-1 / 2 : ℂ) ^ (n / 2) else 0

/-- `v = (0, 1, 0, -1/2, 0, 1/4, …)`. -/
def vSeq (n : ℕ) : ℂ := if n % 2 = 1 then (-1 / 2 : ℂ) ^ (n / 2) else 0

lemma summable_sq_of_le {f : ℕ → ℂ} (h : ∀ n, ‖f n‖ ≤ (1 / 2 : ℝ) ^ (n / 2)) :
    Summable fun n => ‖f n‖ ^ 2 := by
  have hg : Summable fun n : ℕ => ((1 / 2 : ℝ) ^ (n / 2)) ^ 2 := by
    apply Summable.even_add_odd
    · have : (fun k : ℕ => ((1 / 2 : ℝ) ^ (2 * k / 2)) ^ 2) = fun k => (1 / 4 : ℝ) ^ k := by
        ext k
        rw [show 2 * k / 2 = k by omega, ← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [this]
      exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · have : (fun k : ℕ => ((1 / 2 : ℝ) ^ ((2 * k + 1) / 2)) ^ 2) = fun k => (1 / 4 : ℝ) ^ k := by
        ext k
        rw [show (2 * k + 1) / 2 = k by omega, ← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [this]
      exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact hg.of_nonneg_of_le (fun n => by positivity)
    fun n => pow_le_pow_left₀ (norm_nonneg _) (h n) 2

lemma norm_uSeq_le (n : ℕ) : ‖uSeq n‖ ≤ (1 / 2 : ℝ) ^ (n / 2) := by
  unfold uSeq
  split_ifs <;> simp

lemma norm_vSeq_le (n : ℕ) : ‖vSeq n‖ ≤ (1 / 2 : ℝ) ^ (n / 2) := by
  unfold vSeq
  split_ifs <;> simp

/-- `u` in `ℓ²(ℕ)`. -/
def uLp : ℓ²ℕ := ⟨uSeq, memℓp_gen (by simpa using summable_sq_of_le norm_uSeq_le)⟩

/-- `v` in `ℓ²(ℕ)`. -/
def vLp : ℓ²ℕ := ⟨vSeq, memℓp_gen (by simpa using summable_sq_of_le norm_vSeq_le)⟩

lemma uSeq_even (k : ℕ) : uSeq (2 * k) = (-1 / 2 : ℂ) ^ k := by
  unfold uSeq; rw [ite_eq_left (by omega)]; congr 1; omega
lemma uSeq_odd (k : ℕ) : uSeq (2 * k + 1) = 0 := by unfold uSeq; rw [ite_eq_right (by omega)]
lemma vSeq_even (k : ℕ) : vSeq (2 * k) = 0 := by unfold vSeq; rw [ite_eq_right (by omega)]
lemma vSeq_odd (k : ℕ) : vSeq (2 * k + 1) = (-1 / 2 : ℂ) ^ k := by
  unfold vSeq; rw [ite_eq_left (by omega)]; congr 1; omega

lemma jac_uSeq : jac uSeq = 0 := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases k with _ | k
    · simp [jac, Pairing.gen, ptnA, ptnB, κA, κB, uSeq]
    · simp only [jac, Pairing.gen, pairA_ptn, pairA_κ, pairB_ptn, pairB_κ, ptnA_even, ptnB_even,
        uSeq_odd]
      simp
  · simp only [jac, Pairing.gen, pairA_ptn, pairA_κ, pairB_ptn, pairB_κ, ptnA_odd, ptnB_odd,
      κA_odd, κB_odd, uSeq_even, Pi.zero_apply]
    push_cast
    ring

lemma jac_vSeq : jac vSeq = Pi.single 0 1 := by
  ext n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases k with _ | k
    · simp [jac, Pairing.gen, ptnA, ptnB, κA, κB, vSeq]
    · simp only [jac, Pairing.gen, pairA_ptn, pairA_κ, pairB_ptn, pairB_κ, ptnA_even, ptnB_even,
        κA_even, κB_even, vSeq_odd]
      rw [Pi.single_apply, ite_eq_right (by omega)]
      push_cast
      ring
  · simp only [jac, Pairing.gen, pairA_ptn, pairA_κ, pairB_ptn, pairB_κ, ptnA_odd, ptnB_odd,
      vSeq_even]
    rw [Pi.single_apply, ite_eq_right (by omega)]
    simp

/-! ### The restriction to `D` is not essentially self-adjoint -/

lemma finSupp_le_forwardDomain : finSupp ≤ forwardDomain jacobiEvolution := fun _ hx =>
  (differentiable_jacobiEvolution hx 0).differentiableWithinAt

lemma inner_jacLp {x : ℓ²ℕ} (hx : x ∈ finSupp) {u w : ℓ²ℕ} (hw : ⇑w = jac u) :
    ⟪w, x⟫_ℂ = ⟪u, jacLp hx⟫_ℂ := by
  obtain ⟨N, hN⟩ := id hx
  have hs1 : ∀ P : Pairing, Summable fun n => P.gen x n * conj (u n) := fun P =>
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => by
      simp [P.gen_eq_zero hN n (by simpa using hn)]
  have hs2 : ∀ P : Pairing, Summable fun n => x n * conj (P.gen u n) := fun P =>
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by
      simp [hN n (by simpa using hn)]
  simp only [lp.inner_eq_tsum, hw, jacLp_apply, jac, RCLike.inner_apply, map_add, add_mul,
    mul_add]
  rw [(hs2 pairA).tsum_add (hs2 pairB), (hs1 pairA).tsum_add (hs1 pairB),
    pairA.tsum_gen_mul_conj, pairB.tsum_gen_mul_conj]

lemma mem_adjoint_jacobi (ħ : ℝ) {u w : ℓ²ℕ} (hw : ⇑w = jac u) :
    ∃ hu : u ∈ ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp)†.domain,
      ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp)† ⟨u, hu⟩ = (ħ : ℂ) • w := by
  have hdense :
      Dense ((((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).domain :
        Submodule ℂ ℓ²ℕ) : Set ℓ²ℕ) := by
    refine dense_finSupp.mono fun x hx => ?_
    rw [LinearPMap.domRestrict_domain]
    exact ⟨hx, finSupp_le_forwardDomain hx⟩
  have key : ∀ x : ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).domain,
      ⟪(ħ : ℂ) • w, (x : ℓ²ℕ)⟫_ℂ =
        ⟪u, ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp) x⟫_ℂ := by
    intro x
    have hx : (x : ℓ²ℕ) ∈ finSupp := x.2.1
    obtain ⟨hd, h⟩ := forwardHamiltonian_jacobi ħ hx
    have hr : (forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp x =
        forwardHamiltonian jacobiEvolution ħ ⟨x, hd⟩ :=
      LinearPMap.domRestrict_apply (by rfl)
    rw [hr, h, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, inner_jacLp hx hw]
  have hu : u ∈ ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp)†.domain := by
    rw [LinearPMap.mem_adjoint_domain_iff]
    have hc : Continuous fun x : ((forwardHamiltonian jacobiEvolution ħ).domRestrict
        finSupp).domain => ⟪(ħ : ℂ) • w, (x : ℓ²ℕ)⟫_ℂ :=
      continuous_const.inner continuous_subtypeVal
    exact hc.congr fun x => key x
  exact ⟨hu, LinearPMap.adjoint_apply_eq hdense ⟨u, hu⟩ key⟩

/-- **The forward Hamiltonian restricted to `D` is not essentially self-adjoint.** -/
theorem not_isEssentiallySelfAdjoint_jacobi {ħ : ℝ} (hħ : ħ ≠ 0) :
    ¬ ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).IsEssentiallySelfAdjoint := by
  intro hess
  have hsym : ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).IsSymmetric :=
    (forwardHamiltonian_isSymmetric ħ jacobiEvolution_zero fun τ _ =>
      ContinuousLinearMap.inner_map_map_of_mem_unitary (jacobiEvolution_mem_unitary τ)).of_le
      LinearPMap.domRestrict_le
  have hdense : ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).HasDenseDomain := by
    rw [LinearPMap.hasDenseDomain_def]
    refine dense_finSupp.mono fun x hx => ?_
    rw [LinearPMap.domRestrict_domain]
    exact ⟨hx, finSupp_le_forwardDomain hx⟩
  have hadj : ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).closure† =
      ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp)† :=
    (hsym.isUnbounded_iff_hasDenseDomain.mpr hdense).adjoint_closure_eq_adjoint
  have hsa : IsSelfAdjoint ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp)† := by
    rw [← hadj]
    exact LinearPMap.IsSelfAdjoint.adjoint hess
  obtain ⟨hu, hTu⟩ := mem_adjoint_jacobi ħ (u := uLp) (w := 0) (by
    rw [lp.coeFn_zero]
    exact jac_uSeq.symm)
  obtain ⟨hv, hTv⟩ := mem_adjoint_jacobi ħ (u := vLp) (w := lp.single 2 0 1) (by
    rw [lp.coeFn_single]
    exact jac_vSeq.symm)
  have h := LinearPMap.IsSelfAdjoint.isSymmetric hsa ⟨uLp, hu⟩ ⟨vLp, hv⟩
  rw [hTu, hTv, smul_zero, inner_zero_left, inner_smul_right, lp.inner_single_right] at h
  have hu0 : uLp 0 = 1 := by simp [uLp, uSeq]
  rw [hu0] at h
  simp at h
  exact hħ (by exact_mod_cast h.symm)

/-- **Item (iii) has a negative answer.** `F τ = U(τ, 0)` for the unitary propagator
`U(t, s) = e^{-itB} e^{-i(t-s)A} e^{isB}` satisfies every hypothesis of
`QuantumMechanics.isEssentiallySelfAdjoint_forwardHamiltonian` except the bounded differences:
`F 0 = 1`, `F τ` unitary, the finitely supported sequences `D` dense and invariant, and the
orbits on `D` differentiable. The forward Hamiltonian restricted to `D` is not essentially
self-adjoint. -/
theorem jacobi_counterexample {ħ : ℝ} (hħ : ħ ≠ 0) :
    (∀ t s, jacobiPropagator t s ∈ unitary (ℓ²ℕ →L[ℂ] ℓ²ℕ)) ∧
      (∀ t, jacobiPropagator t t = 1) ∧
      (∀ t r s, jacobiPropagator t r * jacobiPropagator r s = jacobiPropagator t s) ∧
      (∀ τ, jacobiEvolution τ = jacobiPropagator τ 0) ∧
      Dense (finSupp : Set ℓ²ℕ) ∧
      (∀ t, ∀ x ∈ finSupp, jacobiEvolution t x ∈ finSupp) ∧
      (∀ x ∈ finSupp, Differentiable ℝ fun t => jacobiEvolution t x) ∧
      ¬ ((forwardHamiltonian jacobiEvolution ħ).domRestrict finSupp).IsEssentiallySelfAdjoint :=
  ⟨jacobiPropagator_mem_unitary, jacobiPropagator_self, jacobiPropagator_mul, jacobiEvolution_eq,
    dense_finSupp, fun t _ hx => jacobiEvolution_mem_finSupp t hx,
    fun _ hx => differentiable_jacobiEvolution hx, not_isEssentiallySelfAdjoint_jacobi hħ⟩

/-- **The bounded-difference condition fails**, as it must: otherwise
`QuantumMechanics.isEssentiallySelfAdjoint_forwardHamiltonian` would apply. -/
theorem not_boundedDifference_jacobi :
    ¬ ∃ C T : ℝ, 0 < T ∧ ∀ t ∈ Icc (-T) T, ∀ x ∈ finSupp,
      ‖deriv (fun s => jacobiEvolution s x) t -
        deriv (fun s => jacobiEvolution s (jacobiEvolution t x)) 0‖ ≤ C * ‖x‖ := by
  rintro ⟨C, T, hT, hC⟩
  exact not_isEssentiallySelfAdjoint_jacobi one_ne_zero
    (isEssentiallySelfAdjoint_forwardHamiltonian one_ne_zero jacobiEvolution_zero
      jacobiEvolution_mem_unitary dense_finSupp (fun t _ hx => jacobiEvolution_mem_finSupp t hx)
      (fun _ hx => differentiable_jacobiEvolution hx) hT hC).1

end UnitaryEntropy
