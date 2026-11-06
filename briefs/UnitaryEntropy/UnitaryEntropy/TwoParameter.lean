/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation: the equation at every time.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a finite-dimensional complex Hilbert space `E` and a two-parameter evolution
`Ψ t₀ t₁ = Φ_{t₀→t₁}`, `t₀ ≤ t₁`, as in `SchroedingerEvolution.TwoParameter.IsEvolution`
(QST:H + [B]EVMIX: affine on density operators, `Ψ t t = id`, the composition law and joint
continuity), without EVTI. `schrodinger_of_preserves` gives the Schrödinger equation at one time,
with unitaries chosen near that time. Here one propagator `U(t)` solves it at every time:
* `DrInfo`  DR-INFO: every `Ψ t₀ t₁` preserves the von Neumann entropy;
* `EvDiff`  EVDIFF: `t ↦ Ψ r t ρ` is differentiable at every `t > r`, for every reference time
  `r` and density operator `ρ`;
* `drSceq_iff_drInfo_and_evDiff`  Theorem 2 at every time: DR-SCEQ with a time-dependent
  Hamiltonian (`SchroedingerEvolution.TwoParameter.DrSceq`) ⇔ DR-INFO + EVDIFF.

Steps of ⇐:
* `exists_unitary`  every `Ψ r t` is induced by a unitary, not an anti-unitary: by Wigner's
  theorem it is one of the two, near each time the maps between nearby times are unitary
  (`eventually_exists_unitary`), so by the composition law the type is locally constant in `t`,
  and `Ψ r r = id`;
* `exists_section`  for each `r`, one differentiable family of unitaries of determinant one
  induces `Ψ r t` for all `t > r` (`QuantumMechanics.Wigner.exists_isDetOneSection`);
* `exists_propagator`  the families for `r = -1, -2, …`, normalized to `1` at `t = 0`, agree
  (they differ by a constant root of unity), and together give `U` with `U 0 = 1`,
  differentiable at every `t`, such that `Ψ t₀ t₁` is conjugation by `U t₁ U t₀†`;
* `H(t) = iħ U'(t) U(t)†` is self-adjoint at every `t`
  (`star_mul_star_eq_neg_of_hasDerivAt_of_mem_unitary`).
-/

public import SchroedingerEvolution.TwoParameter
public import ForPhyslib.QuantumMechanics.Wigner.Propagator

@[expose] public noncomputable section

namespace UnitaryEntropy.TwoParameter

open InnerProductSpace QuantumMechanics.Wigner Filter
open SchroedingerEvolution.TwoParameter (IsEvolution DrSceq)
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

/-! ## Conditions -/

/-- **DR-INFO** for a two-parameter evolution: every `Ψ t₀ t₁` preserves the von Neumann
entropy. -/
def DrInfo (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t₀ t₁, t₀ ≤ t₁ → ∀ ρ, IsDensity ρ → vonNeumann (Ψ t₀ t₁ ρ) = vonNeumann ρ

/-- **EVDIFF** for a two-parameter evolution: for every reference time `r` and density operator
`ρ`, `t ↦ Ψ r t ρ` is differentiable at every `t > r`. -/
def EvDiff (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ r ρ, IsDensity ρ → ∀ t, r < t → DifferentiableAt ℝ (fun s => Ψ r s ρ) t

variable {Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-! ## Every `Ψ r t` is unitary -/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma continuousAt_of_isEvolution (hΨ : IsEvolution Ψ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hfg : ∀ s, f s ≤ g s) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) (x : ℝ) :
    ContinuousAt (fun s => Ψ (f s) (g s) ρ) x := by
  have hc : Continuous fun s => (ρ, f s, g s) := by fun_prop
  have hm : Set.MapsTo (fun s => (ρ, f s, g s)) Set.univ
      {p : (E →L[ℂ] E) × ℝ × ℝ | IsDensity p.1 ∧ p.2.1 ≤ p.2.2} := fun s _ => ⟨hρ, hfg s⟩
  exact (continuousWithinAt_univ _ _).mp
    ((hΨ.continuousOn _ ⟨hρ, hfg x⟩).comp (x := x) hc.continuousWithinAt hm)

omit [CompleteSpace E] in
/-- Wigner's theorem for each `Ψ t₀ t₁`. -/
lemma wigner_of_drInfo (hΨ : IsEvolution Ψ) (hI : DrInfo Ψ) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ t₀ t₁ (proj ψ) = proj (U ψ)) ∨
      ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ t₀ t₁ (proj ψ) = proj (U ψ) :=
  have h := proj_and_trace_of_preserves (Ψ t₀ t₁) (hΨ.isDensity t₀ t₁ h) (hI t₀ t₁ h)
    (fun _ _ hρ hσ => (hΨ.affine t₀ t₁ h).map_mix hρ hσ)
  wigner_rankOne (Ψ t₀ t₁) h.1 h.2

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma implemented_comp {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] {F G : (E →L[ℂ] E) → E →L[ℂ] E}
    {U : E ≃ₛₗᵢ[σ] E} {V : E ≃ₗᵢ[ℂ] E} (hU : ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ))
    (hV : ∀ ψ : E, ‖ψ‖ = 1 → G (proj ψ) = proj (V ψ)) :
    ∀ ψ : E, ‖ψ‖ = 1 → G (F (proj ψ)) = proj ((U.trans V : E ≃ₛₗᵢ[σ] E) ψ) := fun ψ hψ => by
  rw [hU ψ hψ, hV _ (by rw [U.norm_map, hψ])]
  rfl

omit [CompleteSpace E] in
lemma not_unitary_and_antiunitary (h2 : 1 < Module.finrank ℂ E) {F : (E →L[ℂ] E) → E →L[ℂ] E}
    (hU : ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ))
    (hU' : ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ)) : False := by
  obtain ⟨U, hU⟩ := hU
  obtain ⟨U', hU'⟩ := hU'
  refine PhaseEqOnSphere.false_of_unitary_of_antiunitary h2 (f := U) (U' := U')
    (fun v _ => PhaseEq.rfl) fun v hv => ?_
  exact phaseEq_of_rankOne_self_eq (by rw [U.norm_map, hv]) (by rw [U'.norm_map, hv])
    ((hU v hv).symm.trans (hU' v hv))

omit [CompleteSpace E] in
lemma unitary_of_antiunitary (h1 : Module.finrank ℂ E ≤ 1) {F : (E →L[ℂ] E) → E →L[ℂ] E}
    (hU' : ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ) := by
  obtain ⟨U', hU'⟩ := hU'
  refine ⟨LinearIsometryEquiv.refl ℂ E, fun ψ hψ => ?_⟩
  rw [hU' ψ hψ]
  exact (phaseEq_of_finrank_le_one h1 (by rw [U'.norm_map, hψ]) hψ).rankOne_self

omit [CompleteSpace E] in
/-- **Every `Ψ r t` is unitary.** Under DR-INFO each `Ψ r t` is induced by a unitary or an
anti-unitary. Near any `t'`, the maps between `t'` and nearby times are unitary, so by the
composition law `Ψ r t` has the same type as `Ψ r t'`; at `t = r` it is the identity. -/
theorem exists_unitary (hΨ : IsEvolution Ψ) (hI : DrInfo Ψ) {r t : ℝ} (h : r ≤ t) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ r t (proj ψ) = proj (U ψ) := by
  by_cases h2 : 1 < Module.finrank ℂ E
  swap
  · exact (wigner_of_drInfo hΨ hI h).elim id (unitary_of_antiunitary (not_lt.mp h2))
  let Imp : ℝ → Prop := fun s =>
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ r s (proj ψ) = proj (U ψ)
  have hdich : ∀ s, r ≤ s → (Imp s ↔ ¬∃ U : E ≃ₗᵢ⋆[ℂ] E,
      ∀ ψ : E, ‖ψ‖ = 1 → Ψ r s (proj ψ) = proj (U ψ)) := fun s hs =>
    ⟨fun hU hA => not_unitary_and_antiunitary h2 hU hA,
      fun hA => (wigner_of_drInfo hΨ hI hs).resolve_right hA⟩
  -- The type is locally constant near every `t' ≥ r`.
  have hloc : ∀ t', r ≤ t' → ∀ᶠ s in 𝓝 t', r ≤ s → (Imp s ↔ Imp t') := by
    intro t' ht'
    have hK : ∀ᶠ s in 𝓝 t', ∃ V : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 →
        Ψ (min s t') (max s t') (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ) := by
      have hW s := proj_and_trace_of_preserves (Ψ (min s t') (max s t'))
        (hΨ.isDensity _ _ min_le_max) (hI _ _ min_le_max)
        (fun _ _ hρ hσ => (hΨ.affine _ _ min_le_max).map_mix hρ hσ)
      exact eventually_exists_unitary (fun s => (hW s).1) (fun s => (hW s).2)
        (fun ψ hψ => by simpa using hΨ.map_self t' _ (isDensity_proj hψ))
        (fun ψ hψ => continuousAt_of_isEvolution hΨ (continuous_id.min continuous_const)
          (continuous_id.max continuous_const) (fun _ => min_le_max) (isDensity_proj hψ) t')
    filter_upwards [hK] with s ⟨V, hV⟩ hrs
    rcases le_total t' s with hts | hst
    · -- `Ψ r s = Ψ t' s ∘ Ψ r t'`
      have hV' : ∀ ψ : E, ‖ψ‖ = 1 → Ψ t' s (proj ψ) = proj (V ψ) := by
        simpa [min_eq_right hts, max_eq_left hts] using hV
      have hcomp : ∀ ψ : E, ‖ψ‖ = 1 → Ψ r s (proj ψ) = Ψ t' s (Ψ r t' (proj ψ)) :=
        fun ψ hψ => (hΨ.map_comp r t' s ht' hts _ (isDensity_proj hψ)).symm
      constructor
      · intro hs
        rw [hdich t' ht']
        rintro ⟨U, hU⟩
        exact (hdich s hrs).mp hs
          ⟨U.trans V, fun ψ hψ => by rw [hcomp ψ hψ]; exact implemented_comp hU hV' ψ hψ⟩
      · rintro ⟨U, hU⟩
        exact ⟨U.trans V, fun ψ hψ => by rw [hcomp ψ hψ]; exact implemented_comp hU hV' ψ hψ⟩
    · -- `Ψ r t' = Ψ s t' ∘ Ψ r s`
      have hV' : ∀ ψ : E, ‖ψ‖ = 1 → Ψ s t' (proj ψ) = proj (V ψ) := by
        simpa [min_eq_left hst, max_eq_right hst] using hV
      have hcomp : ∀ ψ : E, ‖ψ‖ = 1 → Ψ r t' (proj ψ) = Ψ s t' (Ψ r s (proj ψ)) :=
        fun ψ hψ => (hΨ.map_comp r s t' hrs hst _ (isDensity_proj hψ)).symm
      constructor
      · rintro ⟨U, hU⟩
        exact ⟨U.trans V, fun ψ hψ => by rw [hcomp ψ hψ]; exact implemented_comp hU hV' ψ hψ⟩
      · intro ht
        rw [hdich s hrs]
        rintro ⟨U, hU⟩
        exact (hdich t' ht').mp ht
          ⟨U.trans V, fun ψ hψ => by rw [hcomp ψ hψ]; exact implemented_comp hU hV' ψ hψ⟩
  have hf : IsLocallyConstant fun s => Imp (max s r) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have htend : Tendsto (fun s => max s r) (𝓝 x) (𝓝 (max x r)) :=
      (continuous_id.max continuous_const).tendsto x
    filter_upwards [htend.eventually (hloc _ (le_max_right x r))] with s hs
    exact propext (hs (le_max_right s r))
  have h' := hf.apply_eq_of_preconnectedSpace t r
  simp only [max_eq_left h, max_self] at h'
  change Imp t
  rw [h']
  exact ⟨LinearIsometryEquiv.refl ℂ E, fun ψ hψ => hΨ.map_self r _ (isDensity_proj hψ)⟩

/-! ## The propagator -/

/-- **A section from each reference time.** For every `r`, one differentiable family of unitaries
of determinant one induces `Ψ r t` for all `t > r`. -/
theorem exists_section [Nontrivial E] (hΨ : IsEvolution Ψ) (hI : DrInfo Ψ) (hd : EvDiff Ψ)
    (r : ℝ) : ∃ V : ℝ → E →L[ℂ] E, ∀ t, r < t → IsDetOneSection (fun s => Ψ r (max s r)) V t :=
  exists_isDetOneSection isPreconnected_Ioi isOpen_Ioi
    (fun s => exists_unitary hΨ hI (le_max_right s r))
    fun t ht ψ hψ => (hd r _ (isDensity_proj hψ) t ht).congr_of_eventuallyEq <| by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [max_eq_left (le_of_lt hs)]

/-- A section from the reference time `r < t₀` induces `Ψ t₀ t₁` by `V t₁ V t₀†`. -/
lemma proj_eq_of_section (hΨ : IsEvolution Ψ) {r t₀ t₁ : ℝ} (hr : r < t₀) (h : t₀ ≤ t₁)
    {V : ℝ → E →L[ℂ] E} (hV : ∀ t, r < t → IsDetOneSection (fun s => Ψ r (max s r)) V t) :
    ∀ χ : E, ‖χ‖ = 1 → Ψ t₀ t₁ (proj χ) = proj ((V t₁ * star (V t₀)) χ) := by
  intro χ hχ
  have hu := (hV t₀ hr).1
  have hφ : ‖star (V t₀) χ‖ = 1 := by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hu), hχ]
  have hχφ : V t₀ (star (V t₀) χ) = χ := by
    rw [← mul_apply_eq_comp, Unitary.mul_star_self_of_mem hu, one_apply_eq_self]
  have h₀ := (hV t₀ hr).2.2.1 _ hφ
  have h₁ := (hV t₁ (hr.trans_le h)).2.2.1 _ hφ
  beta_reduce at h₀ h₁
  rw [max_eq_left hr.le, hχφ] at h₀
  rw [max_eq_left (hr.trans_le h).le] at h₁
  rw [← h₀, hΨ.map_comp r t₀ t₁ hr.le h _ (isDensity_proj hφ), h₁]
  rfl

omit [FiniteDimensional ℂ E] in
lemma det_star_eq_one {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) (hd : u.det = 1) :
    (star u).det = 1 := by
  have h := det_mul u (star u)
  rw [Unitary.mul_star_self_of_mem hu, hd, one_mul] at h
  rw [← h]
  exact LinearMap.det_id

/-- **The propagator.** Under DR-INFO and EVDIFF one family of unitaries `U t`, with `U 0 = 1`
and differentiable at every `t`, induces every `Ψ t₀ t₁` on pure states by `U t₁ U t₀†`. -/
theorem exists_propagator [Nontrivial E] (hΨ : IsEvolution Ψ) (hI : DrInfo Ψ) (hd : EvDiff Ψ) :
    ∃ U : ℝ → E →L[ℂ] E, (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ U 0 = 1 ∧
      (∀ t, DifferentiableAt ℝ U t) ∧
      ∀ t₀ t₁, t₀ ≤ t₁ → ∀ χ : E, ‖χ‖ = 1 →
        Ψ t₀ t₁ (proj χ) = proj ((U t₁ * star (U t₀)) χ) := by
  choose V hV using fun n : ℕ => exists_section hΨ hI hd (-(n : ℝ))
  let W : ℕ → ℝ → E →L[ℂ] E := fun n t => V n t * star (V n 0)
  have h0 : ∀ n : ℕ, 1 ≤ n → -(n : ℝ) < 0 := fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  -- The sections from `-m < -n` and from `-n` agree after normalizing at `0`.
  have hWmono : ∀ n m : ℕ, 1 ≤ n → n ≤ m → ∀ t, -(n : ℝ) < t → W n t = W m t := by
    intro n m hn hnm t ht
    rcases hnm.eq_or_lt with rfl | hlt
    · rfl
    have hmn : -(m : ℝ) < -(n : ℝ) := neg_lt_neg (by exact_mod_cast hlt)
    have hA := hV m (-(n : ℝ)) hmn
    have hX : ∀ s ∈ Set.Ioi (-(n : ℝ)),
        IsDetOneSection (fun s => Ψ (-(n : ℝ)) (max s (-(n : ℝ))))
          (fun s => V m s * star (V m (-(n : ℝ)))) s := fun s hs => by
      have hVs := hV m s (hmn.trans hs)
      refine ⟨mul_mem hVs.1 (Unitary.star_mem hA.1), ?_, fun χ hχ => ?_,
        hVs.2.2.2.mul_const _⟩
      · rw [det_mul, hVs.2.1, det_star_eq_one hA.1 hA.2.1, one_mul]
      · beta_reduce
        rw [max_eq_left (le_of_lt hs)]
        exact proj_eq_of_section hΨ hmn (le_of_lt hs) (hV m) χ hχ
    obtain ⟨c, hc, hcX⟩ :=
      IsDetOneSection.exists_eq_smul isPreconnected_Ioi hX (fun s hs => hV n s hs)
    have hc1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc Module.finrank_pos.ne'
    have hcc : c * star c = 1 := by
      rw [Complex.star_def, mul_comm]
      exact conj_mul_self_of_norm_eq_one hc1
    change V n t * star (V n 0) = V m t * star (V m 0)
    rw [hcX t ht, hcX 0 (h0 n hn), star_smul, smul_mul_smul_comm, hcc, one_smul, star_mul,
      star_star, mul_assoc, ← mul_assoc (star (V m (-(n : ℝ)))),
      Unitary.star_mul_self_of_mem hA.1, one_mul]
  have hW : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ t, -(n : ℝ) < t → -(m : ℝ) < t → W n t = W m t := by
    intro n m hn hm t htn htm
    rcases le_total n m with h | h
    · exact hWmono n m hn h t htn
    · exact (hWmono m n hm h t htm).symm
  let N : ℝ → ℕ := fun t => ⌈-t⌉₊ + 1
  have hN : ∀ t, -(N t : ℝ) < t := fun t => by
    have := Nat.le_ceil (-t)
    simp only [N, Nat.cast_add, Nat.cast_one]
    linarith
  have hN1 : ∀ t, 1 ≤ N t := fun t => Nat.le_add_left 1 _
  have hVu : ∀ (n : ℕ) t, -(n : ℝ) < t → V n t ∈ unitary (E →L[ℂ] E) := fun n t ht => (hV n t ht).1
  have hU : ∀ n : ℕ, 1 ≤ n → ∀ t, -(n : ℝ) < t → W (N t) t = W n t :=
    fun n hn t ht => hW _ _ (hN1 t) hn t (hN t) ht
  refine ⟨fun t => W (N t) t, fun t => ?_, ?_, fun t => ?_, fun t₀ t₁ h χ hχ => ?_⟩
  · exact mul_mem (hVu _ t (hN t)) (Unitary.star_mem (hVu _ 0 (h0 _ (hN1 t))))
  · exact Unitary.mul_star_self_of_mem (hVu _ 0 (hN 0))
  · have hev : (fun t => W (N t) t) =ᶠ[𝓝 t] W (N t) := by
      filter_upwards [Ioi_mem_nhds (hN t)] with s hs using hU _ (hN1 t) s hs
    exact (((hV (N t) t (hN t)).2.2.2).mul_const _).congr_of_eventuallyEq hev
  · have hn := hN1 t₀
    have hW₀₁ : W (N t₀) t₁ * star (W (N t₀) t₀) = V (N t₀) t₁ * star (V (N t₀) t₀) := by
      simp only [W, star_mul, star_star]
      rw [mul_assoc, ← mul_assoc (star (V (N t₀) 0)),
        Unitary.star_mul_self_of_mem (hVu _ 0 (h0 _ hn)), one_mul]
    beta_reduce
    rw [hU (N t₀) hn t₁ ((hN t₀).trans_le h), hW₀₁]
    exact proj_eq_of_section hΨ (hN t₀) h (hV (N t₀)) χ hχ

/-! ## Theorem 2 at every time -/

/-- **Theorem 2** at every time: over QST:H + [B]EVMIX for a two-parameter evolution, without
EVTI, DR-SCEQ with a time-dependent Hamiltonian `H(t)` is equivalent to DR-INFO + EVDIFF. For ⇐,
`U` is the propagator of `exists_propagator` and `H(t) = iħ U'(t) U(t)†`. -/
theorem drSceq_iff_drInfo_and_evDiff (hΨ : IsEvolution Ψ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    DrSceq ħ Ψ ↔ DrInfo Ψ ∧ EvDiff Ψ := by
  constructor
  · rintro ⟨H, U, hH, hU₀, hU, hΨU⟩
    have : IsDedekindFiniteMonoid (E →L[ℂ] E) :=
      .of_injective ContinuousLinearMap.toLinearMapRingHom ContinuousLinearMap.coe_injective
    have hu : ∀ t, U t ∈ unitary (E →L[ℂ] E) := fun t =>
      have h := SchroedingerEvolution.TwoParameter.star_mul_self_of_hasDerivAt hH hU₀ hU t
      ⟨h, mul_eq_one_comm.mp h⟩
    refine ⟨fun t₀ t₁ h ρ hρ => ?_, fun r ρ hρ t ht => ?_⟩
    · rw [hΨU t₀ t₁ h ρ hρ]
      exact vonNeumann_unitary_conj (mul_mem (hu t₁) (Unitary.star_mem (hu t₀))) ρ
    · have h1 := (hU t).differentiableAt.mul_const (star (U r))
      refine ((h1.mul_const ρ).mul h1.star).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hΨU r s hs.le ρ hρ
  · rintro ⟨hI, hd⟩
    rcases subsingleton_or_nontrivial E with hE | hE
    · have hs : ∀ A B : E →L[ℂ] E, A = B := fun A B =>
        ContinuousLinearMap.ext fun x => Subsingleton.elim _ _
      exact ⟨fun _ => 0, fun _ => 1, fun _ => .zero _, rfl,
        fun t => by simpa using hasDerivAt_const t (1 : E →L[ℂ] E), fun _ _ _ _ _ => hs _ _⟩
    obtain ⟨U, hu, hU₀, hUd, hΨU⟩ := exists_propagator hΨ hI hd
    have hB : ∀ t, star (deriv U t * star (U t)) = -(deriv U t * star (U t)) := fun t =>
      star_mul_star_eq_neg_of_hasDerivAt_of_mem_unitary hu (hUd t).hasDerivAt
    choose H hH hHB using fun t => exists_hamiltonian_of_star_eq_neg (hB t) hħ
    refine ⟨H, U, hH, hU₀, fun t => ?_, fun t₀ t₁ h ρ hρ => ?_⟩
    · have : (Complex.I * ħ)⁻¹ • (H t * U t) = deriv U t := by
        rw [← smul_mul_assoc, ← hHB t, mul_assoc, Unitary.star_mul_self_of_mem (hu t), mul_one]
      rw [this]
      exact (hUd t).hasDerivAt
    · have hw := mul_mem (hu t₁) (Unitary.star_mem (hu t₀))
      have hW : ∀ χ : E, ‖χ‖ = 1 →
          Ψ t₀ t₁ (proj χ) = proj (Unitary.linearIsometryEquiv ⟨_, hw⟩ χ) := fun χ hχ => by
        show _ = proj ((U t₁ * star (U t₀)) χ)
        exact hΨU t₀ t₁ h χ hχ
      rw [(hΨ.affine t₀ t₁ h).eq_conjOp hW hρ]
      exact (mul_mul_star_eq_conjOp ⟨_, hw⟩ ρ).symm

end UnitaryEntropy.TwoParameter
