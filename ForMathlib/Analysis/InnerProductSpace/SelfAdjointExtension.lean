/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Self-adjoint extensions of real symmetric operators

**Von Neumann's theorem**: a densely defined symmetric operator `T` on a complex Hilbert space
that commutes with a conjugation `C` (an antilinear map with `⟪C x, C y⟫ = ⟪y, x⟫` and `C² = 1`)
has a self-adjoint extension. Schrödinger operators `-Δ + V` with real `V` commute with complex
conjugation, so every one of them that is densely defined has a self-adjoint realization.

## The proof

By Zorn's lemma there is a maximal symmetric extension `S` of `T` among those commuting with `C`
(an increasing union of such extensions is again one). `S` is closed, since `S††` is such an
extension too. If `S† k = i k` for some `k ≠ 0`, then `S† (C k) = -i C k`, and `S` extends
to the symmetric operator `S + span (k + C k)`, still commuting with `C`, with `k + C k ∉ D(S)`;
this is excluded by maximality. Hence `ker (S† ∓ i) = 0`, so the ranges of `S ± i` are dense, and
closed since `S` is closed; then `S` is self-adjoint by von Neumann's criterion.

The criterion and the closed-range lemma are TauCeti's. They are imported privately because
TauCeti and Physlib both declare `LinearPMap.adjoint_smul`: see
`ForMathlib.Analysis.InnerProductSpace.KatoRellich`. Delete the private import, and import TauCeti
publicly, once one of them is renamed.

## Main results

* `LinearPMap.CommutesWithConj`: `T` commutes with `C`.
* `LinearPMap.CommutesWithConj.add`, `LinearPMap.CommutesWithConj.adjoint`: then so do sums and
  `T†`.
* `LinearPMap.exists_isSelfAdjoint_le_of_commutesWithConj`: von Neumann's theorem.

## References

* J. von Neumann, *Allgemeine Eigenwerttheorie Hermitescher Funktionaloperatoren*,
  Math. Ann. **102** (1930), Satz 18.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics II*, Theorem X.3.
-/

@[expose] public section

namespace LinearPMap

open Complex
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `T` commutes with `C`: `C D(T) ⊆ D(T)` and `T C = C T` there. -/
def CommutesWithConj (C : E →ₗ⋆[ℂ] E) (T : E →ₗ.[ℂ] E) : Prop :=
  ∀ x : T.domain, ∃ h : C x ∈ T.domain, T ⟨C x, h⟩ = C (T x)

variable {C : E →ₗ⋆[ℂ] E} {T S : E →ₗ.[ℂ] E}

omit [CompleteSpace E] in
/-- A sum of operators commuting with `C` commutes with `C`. -/
theorem CommutesWithConj.add {A B : E →ₗ.[ℂ] E} (hA : A.CommutesWithConj C)
    (hB : B.CommutesWithConj C) : (A + B).CommutesWithConj C := by
  intro x
  obtain ⟨ha, hA'⟩ := hA ⟨x, x.prop.1⟩
  obtain ⟨hb, hB'⟩ := hB ⟨x, x.prop.2⟩
  refine ⟨⟨ha, hb⟩, ?_⟩
  rw [add_apply, add_apply, C.map_add, ← hA', ← hB']

/-- The adjoint of a densely defined operator commuting with a conjugation `C` commutes with
`C`. -/
theorem CommutesWithConj.adjoint (hC : ∀ x y, ⟪C x, C y⟫_ℂ = ⟪y, x⟫_ℂ) (hCC : ∀ x, C (C x) = x)
    (hT : Dense (T.domain : Set E)) (h : T.CommutesWithConj C) : T†.CommutesWithConj C := by
  intro y
  have key : ∀ x : T.domain, ⟪C (T† y), (x : E)⟫_ℂ = ⟪C y, T x⟫_ℂ := by
    intro x
    obtain ⟨hx, hTx⟩ := h x
    calc ⟪C (T† y), (x : E)⟫_ℂ = ⟪C (T† y), C (C x)⟫_ℂ := by rw [hCC]
      _ = ⟪C x, T† y⟫_ℂ := hC _ _
      _ = conj ⟪T† y, C x⟫_ℂ := (inner_conj_symm _ _).symm
      _ = conj ⟪(y : E), T ⟨C x, hx⟩⟫_ℂ := by
        rw [adjoint_isFormalAdjoint hT y ⟨C x, hx⟩]
      _ = conj ⟪(y : E), C (T x)⟫_ℂ := by rw [hTx]
      _ = ⟪C (T x), y⟫_ℂ := inner_conj_symm _ _
      _ = ⟪C (T x), C (C y)⟫_ℂ := by rw [hCC]
      _ = ⟪C y, T x⟫_ℂ := hC _ _
  exact ⟨mem_adjoint_domain_of_exists _ ⟨_, key⟩, adjoint_apply_eq hT _ key⟩

/-- Taking adjoints reverses extensions. -/
theorem adjoint_le_adjoint (hS : Dense (S.domain : Set E)) (hle : S ≤ T) : T† ≤ S† := by
  have hT : Dense (T.domain : Set E) := hS.mono hle.1
  have h : (T†).IsFormalAdjoint S := fun y x => by
    rw [adjoint_isFormalAdjoint hT y ⟨x, hle.1 x.2⟩, hle.2 (x := x) (y := ⟨x, hle.1 x.2⟩) rfl]
  exact h.symm.le_adjoint hS

/-- An operator contained in its adjoint is symmetric. -/
theorem isFormalAdjoint_of_le_adjoint (hS : Dense (S.domain : Set E)) (h : S ≤ S†) :
    S.IsFormalAdjoint S := fun x y => by
  rw [h.2 (x := x) (y := ⟨x, h.1 x.2⟩) rfl, adjoint_isFormalAdjoint hS]

/-- A densely defined symmetric operator is contained in its closure `S††`, which is again
symmetric. -/
theorem IsFormalAdjoint.le_adjoint_adjoint (hS : Dense (S.domain : Set E))
    (h : S.IsFormalAdjoint S) :
    Dense (S†.domain : Set E) ∧ S ≤ S†† ∧ S††.IsFormalAdjoint S†† := by
  have h1 : S ≤ S† := h.le_adjoint hS
  have hd1 : Dense (S†.domain : Set E) := hS.mono h1.1
  have h2 : S ≤ S†† := (adjoint_isFormalAdjoint hS).le_adjoint hd1
  have hd2 : Dense (S††.domain : Set E) := hS.mono h2.1
  have h3 : S†† ≤ S† := adjoint_le_adjoint hS h1
  have h4 : S† ≤ S††† := (adjoint_isFormalAdjoint hd1).le_adjoint hd2
  exact ⟨hd1, h2, isFormalAdjoint_of_le_adjoint hd2 (h3.trans h4)⟩

omit [CompleteSpace E] in
/-- An element of `D(f) + span x` and the value of `f.supSpanSingleton x y` on it. -/
theorem exists_supSpanSingleton_apply (f : E →ₗ.[ℂ] E) {x : E} (y : E) (hx : x ∉ f.domain)
    (u : (f.supSpanSingleton x y hx).domain) :
    ∃ (x' : E) (hx' : x' ∈ f.domain) (c : ℂ), (u : E) = x' + c • x ∧
      f.supSpanSingleton x y hx u = f ⟨x', hx'⟩ + c • y := by
  have hu : (u : E) ∈ f.domain ⊔ ℂ ∙ x := by
    rw [← domain_supSpanSingleton f x y hx]
    exact u.2
  obtain ⟨x', hx', z, hz, hxz⟩ := Submodule.mem_sup.1 hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  refine ⟨x', hx', c, hxz.symm, ?_⟩
  have : u = ⟨x' + c • x, hxz ▸ u.2⟩ := Subtype.ext hxz.symm
  rw [this, supSpanSingleton_apply_mk f x y hx x' hx' c]
  rfl

omit [CompleteSpace E] in
theorem le_supSpanSingleton (f : E →ₗ.[ℂ] E) {x : E} (y : E) (hx : x ∉ f.domain) :
    f ≤ f.supSpanSingleton x y hx := by
  refine ⟨fun z hz => ?_, fun z w hzw => ?_⟩
  · rw [domain_supSpanSingleton]
    exact Submodule.mem_sup_left hz
  · rw [supSpanSingleton_apply_of_mem _ _ _ w (hzw ▸ z.2)]
    congr 1
    exact Subtype.ext hzw

/-- **The extension step.** A symmetric operator commuting with `C` that is maximal among such
operators has no eigenvector `k ≠ 0` of `S†` for the eigenvalue `i`: otherwise `S` extends to
`D(S) + span (k + C k)`. -/
theorem eq_zero_of_adjoint_apply_eq_I_smul (hC : ∀ x y, ⟪C x, C y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hCC : ∀ x, C (C x) = x) (hd : Dense (S.domain : Set E)) (hS : S.IsFormalAdjoint S)
    (hSC : S.CommutesWithConj C)
    (hmax : ∀ S' : E →ₗ.[ℂ] E, S ≤ S' → S'.IsFormalAdjoint S' → S'.CommutesWithConj C →
      S' ≤ S)
    (k : S†.domain) (hk : S† k = I • (k : E)) : (k : E) = 0 := by
  by_contra hk0
  have hSC' := hSC.adjoint hC hCC hd
  obtain ⟨hck, hSck⟩ := hSC' k
  set ck : S†.domain := ⟨C k, hck⟩
  have hSck' : S† ck = -I • C k := by
    rw [hSck, hk, C.map_smulₛₗ, Complex.conj_I]
  set w : S†.domain := k + ck
  have hw : (w : E) = k + C k := rfl
  have hSw : S† w = I • (k : E) + -I • C k := by rw [map_add, hk, hSck']
  have hCw : C w = w := by rw [hw, C.map_add, hCC, add_comm]
  have hCSw : C (S† w) = S† w := by
    obtain ⟨h, hv⟩ := hSC' w
    rw [← hv]
    congr 1
    exact Subtype.ext hCw
  -- `w ∉ D(S)`
  have hwS : (w : E) ∉ S.domain := by
    intro hwS
    have h1 := adjoint_isFormalAdjoint hd k ⟨w, hwS⟩
    have h2 : S ⟨w, hwS⟩ = S† w :=
      (hS.le_adjoint hd).2 (x := ⟨w, hwS⟩) (y := w) rfl
    rw [h2, hSw, hk, hw] at h1
    simp only [inner_add_right, inner_smul_right, inner_smul_left, Complex.conj_I] at h1
    have h0 : ⟪(k : E), (k : E)⟫_ℂ = 0 := by
      linear_combination (I / 2) * h1 + ⟪(k : E), (k : E)⟫_ℂ * I_sq
    exact hk0 (inner_self_eq_zero.mp h0)
  -- the extension
  set S' := S.supSpanSingleton w (S† w) hwS
  have hle := le_supSpanSingleton S (S† w) hwS
  have hbd : ⟪S† w, (w : E)⟫_ℂ = ⟪(w : E), S† w⟫_ℂ := by
    have hb := hC (k : E) k
    rw [hSw, hw]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_I, conj_neg_I]
    linear_combination (2 * I) * hb
  have hS'sym : S'.IsFormalAdjoint S' := by
    intro u v
    obtain ⟨y, hy, a, hu, hSu⟩ := exists_supSpanSingleton_apply S (S† w) hwS u
    obtain ⟨y', hy', b, hv, hSv⟩ := exists_supSpanSingleton_apply S (S† w) hwS v
    rw [hSu, hSv, hu, hv]
    have e1 := hS ⟨y, hy⟩ ⟨y', hy'⟩
    have e2 : ⟪S ⟨y, hy⟩, (w : E)⟫_ℂ = ⟪y, S† w⟫_ℂ := by
      rw [← inner_conj_symm, ← adjoint_isFormalAdjoint hd w ⟨y, hy⟩, inner_conj_symm]
    have e3 : ⟪S† w, y'⟫_ℂ = ⟪(w : E), S ⟨y', hy'⟩⟫_ℂ := adjoint_isFormalAdjoint hd w ⟨y', hy'⟩
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    linear_combination e1 + b * e2 + conj a * e3 + conj a * b * hbd
  have hS'C : S'.CommutesWithConj C := by
    intro u
    obtain ⟨y, hy, a, hu, hSu⟩ := exists_supSpanSingleton_apply S (S† w) hwS u
    obtain ⟨hcy, hScy⟩ := hSC ⟨y, hy⟩
    have hCu : C u = C y + conj a • (w : E) := by
      rw [hu, C.map_add, C.map_smulₛₗ, hCw]
    have hmem : C u ∈ S'.domain := by
      rw [hCu, domain_supSpanSingleton]
      exact Submodule.add_mem_sup hcy (Submodule.mem_span_singleton.2 ⟨_, rfl⟩)
    refine ⟨hmem, ?_⟩
    have : (⟨C u, hmem⟩ : S'.domain) = ⟨C y + conj a • (w : E), hCu ▸ hmem⟩ := Subtype.ext hCu
    rw [this, supSpanSingleton_apply_mk _ _ _ _ _ hcy, hSu, C.map_add, C.map_smulₛₗ, hScy, hCSw]
    rfl
  have hS'S := hmax S' hle hS'sym hS'C
  exact absurd (hS'S.1 (by
    rw [domain_supSpanSingleton]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))) hwS

/-- A shift `c - S` of a closed symmetric operator, at a nonreal `c` for which `S†` has no
eigenvector for `conj c`, is surjective. -/
theorem surjective_smul_sub_of_ker (hd : Dense (S.domain : Set E)) (hS : S.IsFormalAdjoint S)
    (hcl : S.IsClosed) {c : ℂ} (hc : c.im ≠ 0)
    (hker : ∀ y : S†.domain, S† y = conj c • (y : E) → (y : E) = 0) (φ : E) :
    ∃ x : S.domain, c • (x : E) - S x = φ := by
  have hdr : DenseRange (fun x : S.domain => c • (x : E) - S x) := by
    rw [DenseRange, ← S.coe_range_smulSub c]
    refine Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr ((Submodule.eq_bot_iff _).mpr fun y hy => ?_))
    have hortho : ∀ x : S.domain, inner ℂ y (c • (x : E) - S x) = 0 := fun x =>
      (Submodule.mem_orthogonal' _ y).mp hy _ (LinearMap.mem_range.mpr ⟨x, S.smulSub_apply c x⟩)
    obtain ⟨hy, hSy⟩ := exists_adjoint_apply_eq_of_inner_smul_sub_eq_zero hd hortho
    exact hker ⟨y, hy⟩ hSy
  have hrange := hS.isClosed_range_smul_sub hcl (c := c) hc
  have : φ ∈ Set.range (fun x : S.domain => c • (x : E) - S x) := by
    rw [← hrange.closure_eq]
    exact hdr φ
  exact this

/-- **Von Neumann's theorem.** A densely defined symmetric operator that commutes with a
conjugation has a self-adjoint extension. -/
theorem exists_isSelfAdjoint_le_of_commutesWithConj (hC : ∀ x y, ⟪C x, C y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hCC : ∀ x, C (C x) = x) (hd : Dense (T.domain : Set E)) (hT : T.IsFormalAdjoint T)
    (hTC : T.CommutesWithConj C) : ∃ S, T ≤ S ∧ IsSelfAdjoint S := by
  set 𝒮 : Set (E →ₗ.[ℂ] E) := {S | T ≤ S ∧ S.IsFormalAdjoint S ∧ S.CommutesWithConj C}
  obtain ⟨S, hTS, hmax⟩ := zorn_le_nonempty₀ 𝒮 (fun c hc𝒮 hchain y hy => by
    have hdir := hchain.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    -- every point of the supremum's domain lies in a member, with the same value
    have hmem : ∀ x : (LinearPMap.sSup c hdir).domain, ∃ f ∈ c, ∃ hx : (x : E) ∈ f.domain,
        LinearPMap.sSup c hdir x = f ⟨x, hx⟩ := by
      intro x
      obtain ⟨f, hf, hx⟩ := (mem_domain_sSup_iff hne hdir).1 x.2
      exact ⟨f, hf, hx, LinearPMap.sSup_apply hdir hf ⟨x, hx⟩⟩
    refine ⟨LinearPMap.sSup c hdir, ⟨(hc𝒮 hy).1.trans (LinearPMap.le_sSup hdir hy), ?_, ?_⟩,
      fun z hz => LinearPMap.le_sSup hdir hz⟩
    · intro x x'
      obtain ⟨f, hf, hx, hfx⟩ := hmem x
      obtain ⟨g, hg, hx', hgx⟩ := hmem x'
      obtain ⟨h, hh, hfh, hgh⟩ := hdir f hf g hg
      rw [hfx, hgx, hfh.2 (x := ⟨x, hx⟩) (y := ⟨x, hfh.1 hx⟩) rfl,
        hgh.2 (x := ⟨x', hx'⟩) (y := ⟨x', hgh.1 hx'⟩) rfl]
      exact (hc𝒮 hh).2.1 ⟨x, hfh.1 hx⟩ ⟨x', hgh.1 hx'⟩
    · intro x
      obtain ⟨f, hf, hx, hfx⟩ := hmem x
      obtain ⟨hcx, hfcx⟩ := (hc𝒮 hf).2.2 ⟨x, hx⟩
      refine ⟨(LinearPMap.le_sSup hdir hf).1 hcx, ?_⟩
      rw [hfx, ← hfcx]
      exact LinearPMap.sSup_apply hdir hf ⟨C x, hcx⟩) T ⟨le_rfl, hT, hTC⟩
  obtain ⟨-, hS, hSC⟩ := hmax.1
  have hSmax : ∀ S' : E →ₗ.[ℂ] E, S ≤ S' → S'.IsFormalAdjoint S' → S'.CommutesWithConj C →
      S' ≤ S := fun S' h1 h2 h3 => hmax.2 ⟨hTS.trans h1, h2, h3⟩ h1
  have hdS : Dense (S.domain : Set E) := hd.mono hTS.1
  -- `S` is closed: `S††` is a symmetric extension commuting with `C`
  obtain ⟨hd1, hle2, hsym2⟩ := hS.le_adjoint_adjoint hdS
  have hC2 : S††.CommutesWithConj C :=
    (hSC.adjoint hC hCC hdS).adjoint hC hCC hd1
  have hSeq : S†† = S := le_antisymm (hSmax _ hle2 hsym2 hC2) hle2
  have hcl : S.IsClosed := by
    rw [← hSeq]
    exact adjoint_isClosed hd1
  -- no deficiency vectors
  have hplus : ∀ k : S†.domain, S† k = I • (k : E) → (k : E) = 0 :=
    eq_zero_of_adjoint_apply_eq_I_smul hC hCC hdS hS hSC hSmax
  have hminus : ∀ k : S†.domain, S† k = -I • (k : E) → (k : E) = 0 := by
    intro k hk
    obtain ⟨hck, hSck⟩ := hSC.adjoint hC hCC hdS k
    have h0 := hplus ⟨C k, hck⟩ (by rw [hSck, hk, C.map_smulₛₗ]; simp)
    rw [← hCC k]
    simp only at h0
    rw [h0, C.map_zero]
  refine ⟨S, hTS, isSelfAdjoint_of_surjective_addSub S hS (fun φ => ?_) (fun φ => ?_)⟩
  · obtain ⟨x, hx⟩ := surjective_smul_sub_of_ker hdS hS hcl (c := -I) (by simp)
      (fun y hy => hplus y (by rw [hy]; simp)) (-φ)
    refine ⟨x, ?_⟩
    rw [← neg_neg φ, ← hx]
    simp only [neg_smul]
    abel
  · obtain ⟨x, hx⟩ := surjective_smul_sub_of_ker hdS hS hcl (c := I) (by simp)
      (fun y hy => hminus y (by rw [hy]; simp)) (-φ)
    refine ⟨x, ?_⟩
    rw [← neg_neg φ, ← hx]
    abel

end LinearPMap
