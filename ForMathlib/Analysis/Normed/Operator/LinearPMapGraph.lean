/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Operators on the graph of a partially defined linear map

The graph of a partially defined linear map `f : E →ₗ.[𝕜] F` is a subspace of `E × F`. When it
is closed and `E`, `F` are Banach spaces, it is a Banach space whose norm is equivalent to the
graph norm `‖x‖ + ‖f x‖` of the domain. A bounded operator `A` on `E` that maps the domain of `f`
into itself acts on the graph by `(x, f x) ↦ (A x, f (A x))`, and by the closed graph theorem
this action is bounded (`LinearPMap.graphLift`). A family `A t` is strongly continuous on the
graph exactly when `t ↦ A t x` and `t ↦ f (A t x)` are continuous for `x` in the domain
(`LinearPMap.continuous_graphLift_apply`).

This turns linear evolution equations that preserve the domain of an unbounded operator into
equations on a Banach space, where ODE theory applies.

## Main definitions

* `LinearPMap.graphMk`: the point `(x, f x)` of the graph;
* `LinearPMap.graphFst`: the first coordinate, a bounded operator from the graph to `E`;
* `LinearPMap.graphLift`: a domain-preserving operator, as a bounded operator of the graph.
-/

open Filter Topology

@[expose] public section

namespace LinearPMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E →ₗ.[𝕜] F}

/-- The first coordinate of a point of the graph lies in the domain. -/
lemma fst_mem_domain (y : f.graph) : (y : E × F).1 ∈ f.domain := by
  obtain ⟨z, hz⟩ := (f.mem_graph_iff).mp y.2
  rw [← hz.1]
  exact z.2

/-- The second coordinate of a point of the graph is the value at the first. -/
lemma snd_eq_apply (y : f.graph) : (y : E × F).2 = f ⟨(y : E × F).1, fst_mem_domain y⟩ := by
  obtain ⟨z, hz⟩ := (f.mem_graph_iff).mp y.2
  rw [← hz.2]
  congr 1
  ext
  exact hz.1

/-- Points of the graph are determined by their first coordinate. -/
lemma graph_ext {y z : f.graph} (h : (y : E × F).1 = (z : E × F).1) : y = z := by
  refine Subtype.ext (Prod.ext h ?_)
  rw [snd_eq_apply y, snd_eq_apply z]
  congr 1
  exact Subtype.ext h

/-- The point `(x, f x)` of the graph. -/
def graphMk (x : f.domain) : f.graph := ⟨((x : E), f x), f.mem_graph x⟩

/-- The first coordinate, as a bounded operator from the graph to `E`. -/
def graphFst : f.graph →L[𝕜] E := (ContinuousLinearMap.fst 𝕜 E F).comp f.graph.subtypeL

@[simp] lemma graphFst_apply (y : f.graph) : graphFst y = (y : E × F).1 := rfl

@[simp] lemma graphFst_graphMk (x : f.domain) : graphFst (graphMk x) = (x : E) := rfl

/-- An operator `A` that maps the domain of `f` into itself, as a linear map of the graph. -/
def graphLiftₗ (A : E →L[𝕜] E) (hA : ∀ x ∈ f.domain, A x ∈ f.domain) : f.graph →ₗ[𝕜] f.graph where
  toFun y := graphMk ⟨A (y : E × F).1, hA _ (fst_mem_domain y)⟩
  map_add' y z := graph_ext (by simp [graphMk])
  map_smul' c y := graph_ext (by simp [graphMk])

variable [CompleteSpace f.graph]

/-- An operator `A` that maps the domain of `f` into itself is bounded on a complete graph, by
the closed graph theorem. -/
def graphLift (A : E →L[𝕜] E) (hA : ∀ x ∈ f.domain, A x ∈ f.domain) : f.graph →L[𝕜] f.graph :=
  ⟨graphLiftₗ A hA, (graphLiftₗ A hA).continuous_of_seq_closed_graph fun u x y hu hy => by
    refine graph_ext (tendsto_nhds_unique ((graphFst.continuous.tendsto y).comp hy) ?_)
    exact (A.continuous.comp graphFst.continuous).tendsto x |>.comp hu⟩

@[simp] lemma graphFst_graphLift (A : E →L[𝕜] E) (hA : ∀ x ∈ f.domain, A x ∈ f.domain)
    (y : f.graph) : graphFst (graphLift A hA y) = A (graphFst y) := rfl

lemma graphLift_snd (A : E →L[𝕜] E) (hA : ∀ x ∈ f.domain, A x ∈ f.domain) (y : f.graph) :
    ((graphLift A hA y : f.graph) : E × F).2 = f ⟨A (y : E × F).1, hA _ (fst_mem_domain y)⟩ :=
  rfl

/-- A strongly continuous family `B t` that maps the domain into itself, with `t ↦ f (B t x)`
continuous for `x` in the domain, is strongly continuous on the graph. -/
lemma continuous_graphLift_apply {X : Type*} [TopologicalSpace X] {B : X → E →L[𝕜] E}
    (hB : ∀ t, ∀ x ∈ f.domain, B t x ∈ f.domain) (hBc : ∀ x, Continuous (B · x))
    (hBf : ∀ x : f.domain, Continuous fun t => f ⟨B t x, hB t x x.2⟩) (y : f.graph) :
    Continuous fun t => graphLift (B t) (hB t) y :=
  Continuous.subtype_mk (Continuous.prodMk (hBc _) (hBf ⟨_, fst_mem_domain y⟩)) _

end LinearPMap
