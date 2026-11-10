/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Composition of partially defined linear maps on the natural domain

Mathlib's `LinearPMap.comp g f H` needs a proof `H` that `f` maps all of its domain into the
domain of `g`. For unbounded operators the composition is instead taken on its natural domain,
the vectors `x ∈ f.domain` with `f x ∈ g.domain`; this is how products such as `X P` and
commutators `X P - P X` of unbounded operators are defined.

## Main definitions

* `LinearPMap.compMaxDomain g f`: the natural domain `{x ∈ f.domain | f x ∈ g.domain}`;
* `LinearPMap.compMax g f`: the composition `g ∘ f` on it.

## Main results

* `LinearPMap.mem_domain_compMax`: membership in the domain;
* `LinearPMap.compMax_apply`: `g.compMax f x = g (f x)`;
* `LinearPMap.compMax_domain_le`: the domain lies in `f.domain`.
-/

@[expose] public section

namespace LinearPMap

variable {R E F G : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G]

/-- The natural domain of `g ∘ f`: the vectors `x ∈ f.domain` with `f x ∈ g.domain`. -/
def compMaxDomain (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) : Submodule R E :=
  (g.domain.comap f.toFun).map f.domain.subtype

theorem mem_compMaxDomain {g : F →ₗ.[R] G} {f : E →ₗ.[R] F} {x : E} :
    x ∈ compMaxDomain g f ↔ ∃ h : x ∈ f.domain, f ⟨x, h⟩ ∈ g.domain := by
  simp only [compMaxDomain, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

/-- The composition `g ∘ f` of partially defined linear maps, on its natural domain
`{x ∈ f.domain | f x ∈ g.domain}`. -/
def compMax (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G :=
  g.comp (f.domRestrict (compMaxDomain g f)) fun x => by
    obtain ⟨h, hx⟩ := mem_compMaxDomain.1 x.2.1
    exact hx

theorem domain_compMax (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (g.compMax f).domain = compMaxDomain g f ⊓ f.domain :=
  rfl

theorem mem_domain_compMax {g : F →ₗ.[R] G} {f : E →ₗ.[R] F} {x : E} :
    x ∈ (g.compMax f).domain ↔ ∃ h : x ∈ f.domain, f ⟨x, h⟩ ∈ g.domain := by
  rw [domain_compMax, Submodule.mem_inf, mem_compMaxDomain]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem compMax_domain_le (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) :
    (g.compMax f).domain ≤ f.domain :=
  inf_le_right

theorem compMax_apply {g : F →ₗ.[R] G} {f : E →ₗ.[R] F} (x : (g.compMax f).domain) :
    g.compMax f x =
      g ⟨f ⟨x, (mem_domain_compMax.1 x.2).1⟩, (mem_domain_compMax.1 x.2).2⟩ :=
  rfl

end LinearPMap
