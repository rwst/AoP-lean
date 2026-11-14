/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermitePartialSum

/-!
# Further results: the completeness problem of Definition 1

Not part of the brief. This file formalizes Sec. 2 of `further-results.tex` in the brief's
directory (R. Stephan, *Further results on the brief "Physical vector spaces for quantum
mechanics"*).

The brief leaves open how to exclude two pathological cases of Definition 1 (Sec. 5,
"Completeness of the Lie algebra"): a space carrying the observables of a qubit, with "too many
vectors", and a Schwartz space with position as the only defining observable, with "too few
observables". Here:

* the second case is not a quantum vector space: with position alone, `𝓢(ℝ)` is not complete in
  the topology of Corollary 2;
* the first case is one, and irreducibility excludes it: an operator on `V` that is continuous
  and commutes with every defining observable must be a multiple of the identity. This is
  Roberts's condition that the labelled observables have the same commutant as all observables,
  stated on `V` instead of on a Hilbert completion;
* Examples 3 (in one dimension) and 4 of the brief are irreducible.

## Main results

* `IsIrreducible`  the condition;
* `continuous_of_commute`  an operator that commutes with the defining observables and is
  bounded in the inner-product norm is continuous;
* `isIrreducible_qubit`  Example 4 is irreducible;
* `isQuantumVectorSpace_pair`, `not_isIrreducible_pair`  `ℂ² ⊗ ℂ²` with the observables `Sᵢ ⊗ 1`
  is a quantum vector space, but `1 ⊗ σ₃` commutes with them;
* `not_completeSpace_posOnly`, `not_isQuantumVectorSpace_posOnly`  `𝓢(ℝ)` with position as the
  only defining observable is not complete, so it is not a quantum vector space;
* `not_isIrreducible_posOnly`  nor is it irreducible: the modulation `f ↦ e^{ix} f` commutes
  with position;
* `isIrreducible_schwartz`  Example 3 is irreducible, by the ladder operators and the
  convergence of Hermite expansions in `𝓢(ℝ)` (`SchwartzMap.tendsto_hermiteSum`, in
  `ForMathlib`).

## References

* J. E. Roberts, The Dirac bra and ket formalism, J. Math. Phys. 7 (1966) 1097–1104, Sec. 2,
  p. 1099: "We simply suppose that `𝒪' = 𝒪_l'`, where `𝒪'` denotes the set of all bounded
  operators commuting with `𝒪`", the set of all observables, and `𝒪_l` that of the labelled ones.
* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. II. Symmetry
  problems, J. Math. Phys. 10 (1969) 2276–2290: the space is required to be invariant under a
  unitary representation of the symmetry group, and is built from it.
-/

open Topology Filter
open scoped NNReal

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-! ### Irreducibility -/

section Irreducible

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι : Type*} (X : ι → Module.End ℂ V)

/-- `(V, X)` is irreducible if the only operators on `V` that are continuous for the topology of
Corollary 2 and commute with every defining observable are the multiples of the identity. -/
def IsIrreducible : Prop :=
  ∀ T : Module.End ℂ V, Continuous[topology c X, topology c X] T →
    (∀ i, T * X i = X i * T) → ∃ z : ℂ, T = z • 1

variable {c X}

/-- An operator that commutes with the defining observables commutes with their algebra. -/
lemma commute_of_mem_algebra {T : Module.End ℂ V} (hT : ∀ i, T * X i = X i * T)
    {A : Module.End ℂ V} (hA : A ∈ algebra X) : T * A = A * T := by
  have h : algebra X ≤ Subalgebra.centralizer ℂ {T} :=
    Algebra.adjoin_le fun _ ⟨i, hi⟩ => by
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rw [← hi, hT i]
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h hA) T rfl)

/-- An operator that commutes with the defining observables and is bounded for the inner-product
norm is continuous for the topology of Corollary 2. -/
theorem continuous_of_commute {T : Module.End ℂ V} (hT : ∀ i, T * X i = X i * T) (C : ℝ≥0)
    (hC : ∀ v, c.toSeminorm (T v) ≤ C * c.toSeminorm v) :
    Continuous[topology c X, topology c X] T := by
  let := topology c X
  have hp := withSeminorms c X
  refine WithSeminorms.continuous_of_isBounded hp hp T fun A => ⟨{A}, C, fun v => ?_⟩
  have hA : A.1 (T v) = T (A.1 v) := by
    rw [← mul_apply_eq_comp, ← commute_of_mem_algebra hT A.2, mul_apply_eq_comp]
  rw [Finset.sup_singleton, Seminorm.comp_apply, smul_apply, NNReal.smul_def,
    smul_eq_mul]
  change c.toSeminorm (A.1 (T v)) ≤ C * c.toSeminorm (A.1 v)
  rw [hA]
  exact hC _

/-- If `V` is complete, a sequence that is Cauchy for every seminorm `p_A` converges for every
`p_A`. -/
theorem exists_tendsto_of_completeSpace (hcomp : @CompleteSpace V (uniformSpace c X))
    {u : ℕ → V}
    (hu : ∀ A, ∀ ε > 0, ∀ᶠ p in atTop ×ˢ atTop, seminormFamily c X A (u p.1 - u p.2) < ε) :
    ∃ h, ∀ A, ∀ ε > 0, ∀ᶠ m in atTop, seminormFamily c X A (u m - h) < ε := by
  let := uniformSpace c X
  have hp : WithSeminorms (seminormFamily c X) := withSeminorms c X
  have : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  have hcauchy : CauchySeq u := by
    rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto]
    refine ⟨inferInstance, (hp.tendsto_nhds _ 0).2 fun A ε hε => ?_⟩
    simpa using hu A ε hε
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨h, (hp.tendsto_nhds u h).1 hh⟩

end Irreducible

/-! ### The qubit is irreducible -/

section Qubit

open Matrix Complex
open scoped Kronecker

/-- Example 4 is irreducible: for `ħ ≠ 0`, only the multiples of the identity commute with the
spin observables. -/
theorem isIrreducible_qubit {ħ : ℝ} (hħ : ħ ≠ 0) : IsIrreducible qubitCore (spin ħ) := by
  intro T _ hT
  set M := toEuclideanLin.symm T
  have hTM : T = toEuclideanLin M := by simp [M]
  have hħ2 : (ħ / 2 : ℂ) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hħ) two_ne_zero
  have hcomm (i : Fin 3) : M * pauli i = pauli i * M := by
    have h := hT i
    rw [hTM, spin, ← toEuclideanLin_mul, ← toEuclideanLin_mul] at h
    have h' := toEuclideanLin.injective h
    rw [Matrix.mul_smul, Matrix.smul_mul] at h'
    exact smul_right_injective _ hħ2 h'
  have e (i : Fin 3) (a b : Fin 2) := congrFun₂ (hcomm i) a b
  have h01 := e 2 0 1
  have h10 := e 2 1 0
  have h00 := e 0 0 1
  simp [pauli, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10 h00
  refine ⟨M 0 0, ?_⟩
  have hM : M = M 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
    all_goals first | linear_combination -h01 / 2 | linear_combination h10 / 2 | linear_combination -h00
  rw [hTM]
  nth_rewrite 1 [hM]
  rw [map_smul]
  congr 1
  ext v
  simp

end Qubit

/-! ### Too many vectors: the qubit observables on `ℂ² ⊗ ℂ²` -/

section QubitPair

open Matrix Complex
open scoped Kronecker

/-- The space `ℂ² ⊗ ℂ²`. -/
abbrev Pair := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The inner product of `ℂ² ⊗ ℂ²`. -/
abbrev pairCore : PreInnerProductSpace.Core ℂ Pair := PreInnerProductSpace.toCore

/-- The spin observables of the first factor, `Sᵢ ⊗ 1`. -/
def spinPair (ħ : ℝ) (i : Fin 3) : Module.End ℂ Pair :=
  toEuclideanLin (((ħ / 2 : ℂ) • pauli i) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))

lemma sub_kronecker_one (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) - B ⊗ₖ 1 = (A - B) ⊗ₖ 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [sub_mul]

theorem spinPair_comm (ħ : ℝ) (i : Fin 3) :
    spinPair ħ i * spinPair ħ (i + 1) - spinPair ħ (i + 1) * spinPair ħ i =
      (I * ħ) • spinPair ħ (i + 2) := by
  simp only [spinPair, ← toEuclideanLin_mul, ← map_sub, ← map_smul, ← mul_kronecker_mul,
    Matrix.one_mul, sub_kronecker_one, ← smul_kronecker]
  congr 2
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, pauli_comm, smul_smul, smul_smul]
  congr 1
  ring

theorem isSymmetric_spinPair (ħ : ℝ) (i : Fin 3) : IsSymmetric pairCore (spinPair ħ i) := by
  refine isSymmetric_toEuclideanLin_iff.mpr ?_
  rw [IsHermitian, conjTranspose_kronecker, (isHermitian_spinMatrix ħ i).eq, conjTranspose_one]

theorem topology_pair {ι : Type*} (X : ι → Module.End ℂ Pair) :
    topology pairCore X = (inferInstance : TopologicalSpace Pair) := by
  rw [topology_eq_moduleTopology pairCore X fun v hv => inner_self_eq_zero.mp hv]
  have := isModuleTopologyOfFiniteDimensional (𝕜 := ℂ) (E := Pair)
  exact (eq_moduleTopology ℂ _).symm

/-- `ℂ² ⊗ ℂ²` with the spin observables of the first factor is a quantum vector space. -/
theorem isQuantumVectorSpace_pair (ħ : ℝ) :
    IsQuantumVectorSpace pairCore (spinPair ħ) ħ levi where
  isSymmetric := isSymmetric_spinPair ħ
  comm i j := by
    have h0 := spinPair_comm ħ 0
    have h1 := spinPair_comm ħ 1
    have h2 := spinPair_comm ħ 2
    fin_cases i <;> fin_cases j <;> simp [levi] at h0 h1 h2 ⊢
    all_goals first | assumption | (rw [← neg_sub]; congr 1)
  completeSpace := by
    rw [uniformSpace_eq pairCore (spinPair ħ) (topology_pair _)]
    infer_instance
  secondCountableTopology := by
    rw [topology_pair]
    infer_instance

/-- But it is not irreducible: `1 ⊗ σ₃` commutes with every `Sᵢ ⊗ 1`. -/
theorem not_isIrreducible_pair (ħ : ℝ) : ¬ IsIrreducible pairCore (spinPair ħ) := by
  intro h
  obtain ⟨z, hz⟩ := h (toEuclideanLin ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli 2))
    (by rw [topology_pair]; exact LinearMap.continuous_of_finiteDimensional _) fun i => by
      rw [spinPair, ← toEuclideanLin_mul, ← toEuclideanLin_mul, ← mul_kronecker_mul,
        ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  have hz' : (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli 2 = z • 1 := by
    apply toEuclideanLin.injective
    rw [hz, map_smul]
    congr 1
    ext v
    simp
  have e0 := congrFun₂ hz' (0, 0) (0, 0)
  have e1 := congrFun₂ hz' (0, 1) (0, 1)
  simp [pauli] at e0 e1
  rw [← e0] at e1
  norm_num at e1

end QubitPair

/-! ### The ground state and `L²` bounds on `𝓢(ℝ)` -/

section Hermite

open SchwartzMap MeasureTheory

/-- `ψ₀(x) = π^{-1/4} e^{-x²/2}`. -/
def gaussReal (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2)) / √(√Real.pi)

lemma gaussReal_pos (x : ℝ) : 0 < gaussReal x := by unfold gaussReal; positivity

lemma hermite_zero_apply (x : ℝ) : hermite 0 x = (gaussReal x : ℂ) := by
  rw [hermite_apply, TauCeti.hermiteFunction_zero, gaussReal]

/-- A pointwise bound gives an `L²` bound. -/
lemma l2Core_toSeminorm_le {f g : 𝓢(ℝ, ℂ)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    l2Core.toSeminorm f ≤ C * l2Core.toSeminorm g := by
  rw [l2Core_toSeminorm, l2Core_toSeminorm, ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g.memLp 2).eLpNorm_ne_top)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by fun_prop) (Eventually.of_forall h) 2)

lemma eLpNorm_eq_ofReal (f : 𝓢(ℝ, ℂ)) :
    eLpNorm f 2 volume = ENNReal.ofReal (l2Core.toSeminorm f) := by
  rw [l2Core_toSeminorm]
  exact (ENNReal.ofReal_toReal (f.memLp 2).eLpNorm_ne_top).symm

end Hermite

/-! ### Too few observables: position alone on `𝓢(ℝ)` -/

section PositionOnly

open SchwartzMap MeasureTheory Complex

/-- Position as the only defining observable on `𝓢(ℝ)`. -/
def posOnly : Unit → Module.End ℂ 𝓢(ℝ, ℂ) := fun _ => posOp

/-- Multiplication by a function `g` (of temperate growth). -/
def mulOp (g : ℝ → ℂ) : Module.End ℂ 𝓢(ℝ, ℂ) := (smulLeftCLM ℂ g).toLinearMap

lemma mulOp_apply {g : ℝ → ℂ} (hg : g.HasTemperateGrowth) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    mulOp g f x = g x * f x :=
  smulLeftCLM_apply_apply hg f x

lemma mulOp_mul_posOp {g : ℝ → ℂ} (hg : g.HasTemperateGrowth) :
    mulOp g * posOp = posOp * mulOp g := by
  ext f x
  simp only [mul_apply_eq_comp, mulOp_apply hg, posOp_apply]
  ring

/-- Position alone is not irreducible on `𝓢(ℝ)`: the modulation `f ↦ e^{ix} f` commutes with it. -/
theorem not_isIrreducible_posOnly : ¬ IsIrreducible l2Core posOnly := by
  intro h
  have hg := hasTemperateGrowth_exp_mul_I
  obtain ⟨z, hz⟩ := h (mulOp fun x : ℝ => exp (x * I))
    (continuous_of_commute (fun _ => mulOp_mul_posOp hg) 1 fun f =>
      l2Core_toSeminorm_le zero_le_one fun x => by simp [mulOp_apply hg, norm_exp_ofReal_mul_I])
    fun _ => mulOp_mul_posOp hg
  have e (x : ℝ) := congrArg (fun f : 𝓢(ℝ, ℂ) => f x) (LinearMap.congr_fun hz (hermite 0))
  have e0 := e 0
  have e1 := e Real.pi
  simp only [mulOp_apply hg, LinearMap.smul_apply, one_apply_eq_self, smul_apply,
    smul_eq_mul, hermite_zero_apply] at e0 e1
  have h0 := ofReal_ne_zero.mpr (gaussReal_pos 0).ne'
  have hπ := ofReal_ne_zero.mpr (gaussReal_pos Real.pi).ne'
  simp only [ofReal_zero, zero_mul, exp_zero] at e0
  rw [exp_pi_mul_I] at e1
  have hz1 : z = 1 := (mul_right_cancel₀ h0 e0).symm
  have hz2 : z = -1 := (mul_right_cancel₀ hπ e1).symm
  rw [hz1] at hz2
  norm_num at hz2

/-- `uₜ(x) = √(t⁻² + x²)`, written so that it visibly has temperate growth. -/
def kink (t x : ℝ) : ℂ := ((t⁻¹ * (1 + ‖t * x‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

lemma hasTemperateGrowth_kink (t : ℝ) : (kink t).HasTemperateGrowth := by
  have h1 : (fun x : ℝ => t * x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const t).mul Function.HasTemperateGrowth.id'
  have h2 := (Function.HasTemperateGrowth.const t⁻¹).mul
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow (H := ℝ) (1 / 2)).comp h1)
  exact Complex.hasTemperateGrowth_ofReal.comp h2

lemma kink_eq {t : ℝ} (ht : 0 < t) (x : ℝ) : kink t x = (‖((t⁻¹ : ℝ) : ℂ) + x * I‖ : ℂ) := by
  rw [kink, norm_add_mul_I, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs,
    show t⁻¹ ^ 2 + x ^ 2 = t⁻¹ ^ 2 * (1 + (t * x) ^ 2) by field_simp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 ht.le)]

lemma norm_kink_sub_kink_le {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (x : ℝ) :
    ‖kink t x - kink s x‖ ≤ |t⁻¹ - s⁻¹| := by
  rw [kink_eq ht, kink_eq hs, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [add_sub_add_right_eq_sub, ← ofReal_sub, norm_real, Real.norm_eq_abs]

lemma norm_kink_sub_abs_le {t : ℝ} (ht : 0 < t) (x : ℝ) : ‖kink t x - |x|‖ ≤ t⁻¹ := by
  have hx : (|x| : ℝ) = ‖(x : ℂ) * I‖ := by simp
  rw [kink_eq ht, hx, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [add_sub_cancel_right, norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]

/-- The Schwartz functions `fₘ = √((m+1)⁻² + x²) ψ₀`, which tend to `|x| ψ₀`. -/
def kinkSeq (m : ℕ) : 𝓢(ℝ, ℂ) := mulOp (kink ((m : ℝ) + 1)) (hermite 0)

lemma seminormFamily_kinkSeq_sub_le (A : algebra posOnly) (m n : ℕ) :
    seminormFamily l2Core posOnly A (kinkSeq m - kinkSeq n) ≤
      |((m : ℝ) + 1)⁻¹ - ((n : ℝ) + 1)⁻¹| * l2Core.toSeminorm (A.1 (hermite 0)) := by
  have hc (t : ℝ) := commute_of_mem_algebra (X := posOnly)
    (fun _ => mulOp_mul_posOp (hasTemperateGrowth_kink t)) A.2
  have hA : A.1 (kinkSeq m - kinkSeq n) =
      mulOp (kink ((m : ℝ) + 1)) (A.1 (hermite 0)) - mulOp (kink ((n : ℝ) + 1)) (A.1 (hermite 0)) := by
    rw [kinkSeq, kinkSeq, map_sub, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← hc, ← hc,
      mul_apply_eq_comp, mul_apply_eq_comp]
  change l2Core.toSeminorm (A.1 (kinkSeq m - kinkSeq n)) ≤ _
  rw [hA]
  refine l2Core_toSeminorm_le (abs_nonneg _) fun x => ?_
  rw [sub_apply, mulOp_apply (hasTemperateGrowth_kink _), mulOp_apply (hasTemperateGrowth_kink _),
    ← sub_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_kink_sub_kink_le (by positivity) (by positivity) x)
    (norm_nonneg _)

/-- The brief's second pathological example is not a quantum vector space: with position as the
only defining observable, `𝓢(ℝ)` is not complete. The sequence `kinkSeq` is Cauchy, and its limit
would be `|x| ψ₀`, which is not differentiable at `0`. -/
theorem not_completeSpace_posOnly : ¬ @CompleteSpace 𝓢(ℝ, ℂ) (uniformSpace l2Core posOnly) := by
  intro hcomp
  have hε : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  obtain ⟨h, hh⟩ := exists_tendsto_of_completeSpace hcomp (u := kinkSeq) fun A ε hε0 => by
    have h2 : Tendsto (fun p : ℕ × ℕ => |((p.1 : ℝ) + 1)⁻¹ - ((p.2 : ℝ) + 1)⁻¹| *
        l2Core.toSeminorm (A.1 (hermite 0))) (atTop ×ˢ atTop) (𝓝 0) := by
      simpa using (((hε.comp tendsto_fst).sub (hε.comp tendsto_snd)).abs.mul_const
        (l2Core.toSeminorm (A.1 (hermite 0))))
    filter_upwards [h2.eventually (gt_mem_nhds hε0)] with p hp'
    exact (seminormFamily_kinkSeq_sub_le A p.1 p.2).trans_lt hp'
  have hL2 : Tendsto (fun m => l2Core.toSeminorm (kinkSeq m - h)) atTop (𝓝 0) := by
    have h1 := hh 1
    rw [seminormFamily_one] at h1
    exact tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun m => ha.trans_le (apply_nonneg _ _),
      h1⟩
  -- `h = |x| ψ₀` almost everywhere, hence everywhere
  set F : ℝ → ℂ := fun x => ((|x| : ℝ) : ℂ) * hermite 0 x
  have hFc : Continuous F := by fun_prop
  have hbound (m : ℕ) : eLpNorm (⇑h - F) 2 volume ≤ ENNReal.ofReal
      (l2Core.toSeminorm (kinkSeq m - h) + ((m : ℝ) + 1)⁻¹ * l2Core.toSeminorm (hermite 0)) := by
    have hsplit : ⇑h - F = (⇑h - ⇑(kinkSeq m)) + (⇑(kinkSeq m) - F) := by abel
    rw [hsplit, ENNReal.ofReal_add (apply_nonneg _ _) (by positivity)]
    refine (eLpNorm_add_le one_le_two).trans (add_le_add ?_ ?_)
    · rw [eLpNorm_sub_comm]
      exact (eLpNorm_eq_ofReal (kinkSeq m - h)).le
    · rw [ENNReal.ofReal_mul (by positivity), ← eLpNorm_eq_ofReal]
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by fun_prop) (Eventually.of_forall fun x => ?_) 2
      simp only [Pi.sub_apply, kinkSeq, mulOp_apply (hasTemperateGrowth_kink _), F, ← sub_mul,
        norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_kink_sub_abs_le (by positivity) x) (norm_nonneg _)
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal
      (l2Core.toSeminorm (kinkSeq m - h) + ((m : ℝ) + 1)⁻¹ * l2Core.toSeminorm (hermite 0)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hL2.add (hε.mul_const (l2Core.toSeminorm (hermite 0))))
  have hzero : eLpNorm (⇑h - F) 2 volume = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  rw [eLpNorm_eq_zero_iff two_ne_zero] at hzero
  have hhF : ⇑h = F := (h.continuous.ae_eq_iff_eq volume hFc).1 (by
    filter_upwards [hzero] with x hx
    simpa [sub_eq_zero] using hx)
  -- but `|x| = re (h x) / ψ₀(x)` would be differentiable at `0`
  have hd : DifferentiableAt ℝ (fun x => (h x).re / gaussReal x) 0 :=
    (reCLM.differentiableAt.comp 0 h.differentiableAt).div (by unfold gaussReal; fun_prop)
      (gaussReal_pos 0).ne'
  refine not_differentiableAt_abs_zero (hd.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_))
  simp only [hhF, F, hermite_zero_apply, ← ofReal_mul, ofReal_re]
  rw [mul_div_assoc, div_self (gaussReal_pos x).ne', mul_one]

/-- So the brief's "Schwartz space with only position in the defining observables" is not a
quantum vector space: Definition 1 already excludes it, through completeness. -/
theorem not_isQuantumVectorSpace_posOnly (ħ : ℝ) (C : Unit → Unit → Unit →₀ ℂ) :
    ¬ IsQuantumVectorSpace l2Core posOnly ħ C :=
  fun h => not_completeSpace_posOnly h.completeSpace

end PositionOnly

/-! ### Example 3 is irreducible -/

section HermiteExpansion

open SchwartzMap MeasureTheory Complex ComplexConjugate
open scoped InnerProductSpace

/-- `f ↦ f.toLp 2`, as a continuous linear map. -/
abbrev toL2 : 𝓢(ℝ, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) := toLpCLM ℂ ℂ 2 volume

lemma l2Core_inner_eq (f g : 𝓢(ℝ, ℂ)) : l2Core.inner f g = ⟪toL2 f, toL2 g⟫_ℂ := rfl

/-- The derivative `D f = f'`. -/
def derivOp : Module.End ℂ 𝓢(ℝ, ℂ) := (derivCLM ℂ ℂ).toLinearMap

lemma derivOp_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : derivOp f x = deriv f x := rfl

/-- `D` is antisymmetric. -/
lemma l2Core_inner_derivOp (f g : 𝓢(ℝ, ℂ)) :
    l2Core.inner (derivOp f) g = -l2Core.inner f (derivOp g) := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap
  have hL : ∀ u v, L u v = conj u * v := fun _ _ => by simp [L]
  have hibp := integral_bilinear_deriv_right_eq_neg_left f g L
  simp only [hL] at hibp
  simp only [l2Core_inner, derivOp_apply]
  rw [hibp, neg_neg]

/-- The ladder operators, up to the factor `1/√2`: `a₋ = X + D`, `a₊ = X - D`. -/
def lowerOp : Module.End ℂ 𝓢(ℝ, ℂ) := posOp + derivOp

@[inherit_doc lowerOp]
def raiseOp : Module.End ℂ 𝓢(ℝ, ℂ) := posOp - derivOp

lemma deriv_hermite (n : ℕ) (x : ℝ) :
    deriv (hermite n) x = ((deriv (TauCeti.hermiteFunction n) x : ℝ) : ℂ) := by
  have h : ⇑(hermite n) = fun x => (TauCeti.hermiteFunction n x : ℂ) := funext (hermite_apply n)
  rw [h, ((TauCeti.hasDerivAt_hermiteFunction n x).ofReal_comp).deriv,
    TauCeti.deriv_hermiteFunction]

/-- `a₋ ψₙ = √(2n) ψₙ₋₁`. -/
lemma lowerOp_hermite (n : ℕ) :
    lowerOp (hermite n) = (√(2 * (n : ℝ)) : ℂ) • hermite (n - 1) := by
  ext x
  simp only [lowerOp, LinearMap.add_apply, add_apply, posOp_apply, derivOp_apply, deriv_hermite,
    hermite_apply, smul_apply, smul_eq_mul]
  exact_mod_cast TauCeti.mul_add_deriv_hermiteFunction n x

/-- `a₊ ψₙ = √(2(n+1)) ψₙ₊₁`. -/
lemma raiseOp_hermite (n : ℕ) :
    raiseOp (hermite n) = (√(2 * ((n : ℝ) + 1)) : ℂ) • hermite (n + 1) := by
  ext x
  simp only [raiseOp, LinearMap.sub_apply, sub_apply, posOp_apply, derivOp_apply, deriv_hermite,
    hermite_apply, smul_apply, smul_eq_mul]
  exact_mod_cast TauCeti.mul_sub_deriv_hermiteFunction n x

/-- The Hermite coefficient `cₙ(f) = ⟨ψₙ, f⟩`. -/
def coef (n : ℕ) (f : 𝓢(ℝ, ℂ)) : ℂ := ⟪TauCeti.hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ

lemma coef_eq (n : ℕ) (f : 𝓢(ℝ, ℂ)) : coef n f = l2Core.inner (hermite n) f := by
  rw [coef, l2Core_inner_eq, toLpCLM_apply, toLpCLM_apply, toLp_hermite]

/-- `cₙ(a₋ f) = √(2(n+1)) cₙ₊₁(f)`. -/
lemma coef_lowerOp (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    coef n (lowerOp f) = √(2 * ((n : ℝ) + 1)) * coef (n + 1) f := by
  have hsym : l2Core.inner (hermite n) (posOp f) = l2Core.inner (posOp (hermite n)) f :=
    (isSymmetric_posOp _ _).symm
  rw [coef_eq, coef_eq, lowerOp, LinearMap.add_apply, l2Core_inner_eq, map_add, inner_add_right,
    ← l2Core_inner_eq, ← l2Core_inner_eq, hsym,
    ← neg_neg (l2Core.inner (hermite n) (derivOp f)), ← l2Core_inner_derivOp,
    l2Core_inner_eq, l2Core_inner_eq, ← sub_eq_add_neg, ← inner_sub_left, ← map_sub,
    ← LinearMap.sub_apply, ← raiseOp, raiseOp_hermite, map_smul, inner_smul_left, conj_ofReal]
  rfl

lemma momOp_eq (ħ : ℝ) : momOp ħ = (-I * ħ) • derivOp := rfl

lemma derivOp_eq {ħ : ℝ} (hħ : ħ ≠ 0) : derivOp = ((ħ : ℂ)⁻¹ * I) • momOp ħ := by
  have hħ' : (ħ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hħ
  have h : (ħ : ℂ)⁻¹ * I * (-I * ħ) = 1 := by
    calc (ħ : ℂ)⁻¹ * I * (-I * ħ) = -(I * I) * ((ħ : ℂ)⁻¹ * ħ) := by ring
      _ = 1 := by rw [I_mul_I, inv_mul_cancel₀ hħ']; ring
  rw [momOp_eq, smul_smul, h, one_smul]

lemma lowerOp_mem {ħ : ℝ} (hħ : ħ ≠ 0) : lowerOp ∈ algebra (obs ħ) := by
  have hX : posOp ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨0, rfl⟩
  have hP : momOp ħ ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨1, rfl⟩
  rw [lowerOp, derivOp_eq hħ]
  exact Subalgebra.add_mem _ hX (Subalgebra.smul_mem _ hP _)

lemma raiseOp_mem {ħ : ℝ} (hħ : ħ ≠ 0) : raiseOp ∈ algebra (obs ħ) := by
  have hX : posOp ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨0, rfl⟩
  have hP : momOp ħ ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨1, rfl⟩
  rw [raiseOp, derivOp_eq hħ]
  exact Subalgebra.sub_mem _ hX (Subalgebra.smul_mem _ hP _)

/-- The kernel of `a₋` is spanned by `ψ₀`. -/
lemma eq_smul_hermite_zero {g : 𝓢(ℝ, ℂ)} (hg : lowerOp g = 0) : g = coef 0 g • hermite 0 := by
  have hc (n : ℕ) : coef (n + 1) g = 0 := by
    have h := coef_lowerOp n g
    rw [hg, coef, ← toLpCLM_apply (𝕜 := ℂ), map_zero, inner_zero_right, eq_comm,
      mul_eq_zero] at h
    exact h.resolve_left (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity)))
  have hS : ∀ m ≥ 1, hermiteSum m g = coef 0 g • hermite 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hc' (n : ℕ) : ⟪TauCeti.hermiteFunctionLp ℂ (n + 1), g.toLp 2⟫_ℂ = 0 := hc n
    simp only [hermiteSum, Finset.sum_range_succ', hc', zero_smul, Finset.sum_const_zero,
      zero_add]
    rfl
  exact tendsto_nhds_unique (tendsto_hermiteSum g)
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun m hm => (hS m hm).symm⟩))

/-- **Example 3 is irreducible**: for `ħ ≠ 0`, the only continuous operators on `𝓢(ℝ)` that
commute with `X` and `P` are the multiples of the identity. -/
theorem isIrreducible_schwartz {ħ : ℝ} (hħ : ħ ≠ 0) : IsIrreducible l2Core (obs ħ) := by
  intro T hTc hT
  rw [topology_schwartz ħ hħ] at hTc
  have hl : T * lowerOp = lowerOp * T := commute_of_mem_algebra hT (lowerOp_mem hħ)
  have hr : T * raiseOp = raiseOp * T := commute_of_mem_algebra hT (raiseOp_mem hħ)
  set z := coef 0 (T (hermite 0))
  have hn (n : ℕ) : T (hermite n) = z • hermite n := by
    induction n with
    | zero =>
      refine eq_smul_hermite_zero ?_
      rw [← mul_apply_eq_comp, ← hl, mul_apply_eq_comp, lowerOp_hermite]
      simp
    | succ n ih =>
      have h := congrArg T (raiseOp_hermite n)
      rw [← mul_apply_eq_comp, hr, mul_apply_eq_comp, ih, map_smul, raiseOp_hermite, map_smul,
        smul_comm] at h
      exact smul_right_injective _ (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity)))
        h.symm
  have hS (m : ℕ) (f : 𝓢(ℝ, ℂ)) : T (hermiteSum m f) = z • hermiteSum m f := by
    simp only [hermiteSum, map_sum, map_smul, hn, Finset.smul_sum, smul_comm z]
  refine ⟨z, LinearMap.ext fun f => ?_⟩
  have h1 := (hTc.tendsto f).comp (tendsto_hermiteSum f)
  simp only [Function.comp_def, hS] at h1
  rw [LinearMap.smul_apply, one_apply_eq_self]
  exact tendsto_nhds_unique h1 ((tendsto_hermiteSum f).const_smul z)

end HermiteExpansion

end QuantumVectorSpaces.FurtherResults
