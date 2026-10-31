/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Composition of bounded linear maps between seminormed families

`Seminorm.IsBounded p q f` says that every seminorm `q i ∘ f` is bounded by finitely many of the
`p j`. This file proves that the relation is transitive, so that equivalence of seminorm
families can be shown along a cycle `p → q → r → p`.

## Main results

* `Seminorm.IsBounded.comp`: bounded maps compose;
* `WithSeminorms.congr_of_cycle`: if `p` bounds `q`, `q` bounds `r` and `r` bounds `p` (all via
  the identity), then all three families generate the same topology.
-/

open scoped NNReal

@[expose] public section

namespace Seminorm

variable {𝕜 E F G ι ι' ι'' : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [AddCommGroup G] [Module 𝕜 G]

theorem IsBounded.comp {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 F} {r : ι'' → Seminorm 𝕜 G}
    {f : E →ₗ[𝕜] F} {g : F →ₗ[𝕜] G} (hg : IsBounded q r g) (hf : IsBounded p q f) :
    IsBounded p r (g ∘ₗ f) := by
  intro i
  obtain ⟨s, C, hC⟩ := hg i
  obtain ⟨C', s', hC'⟩ := isBounded_sup hf s
  refine ⟨s', C * C', fun x => ?_⟩
  calc r i (g (f x)) ≤ C * (s.sup q) (f x) := hC (f x)
    _ ≤ C * (C' * (s'.sup p) x) := by gcongr; exact hC' x
    _ = (C * C') • (s'.sup p) x := by rw [NNReal.smul_def, smul_eq_mul]; push_cast; ring

end Seminorm

namespace WithSeminorms

variable {𝕜 E ι ι' ι'' : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Three seminorm families that bound each other along a cycle generate the same topology. -/
theorem congr_of_cycle {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}
    {r : SeminormFamily 𝕜 E ι''} [TopologicalSpace E] (hp : WithSeminorms p)
    (hpq : Seminorm.IsBounded p q LinearMap.id) (hqr : Seminorm.IsBounded q r LinearMap.id)
    (hrp : Seminorm.IsBounded r p LinearMap.id) : WithSeminorms q ∧ WithSeminorms r :=
  ⟨hp.congr hpq (hrp.comp hqr), hp.congr (hqr.comp hpq) hrp⟩

end WithSeminorms
