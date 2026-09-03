import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq

set_option autoImplicit false
open scoped TensorProduct

theorem LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
    {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] [Nontrivial k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V] (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤) :
    Module.finrank k (k ⊗[R] V) = 2 ∧
    Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) = ⊤ ∧
    (∀ g : G, LinearMap.trace k (k ⊗[R] V) ((ρV g).baseChange k) = algebraMap R k (LinearMap.trace R V (ρV g))) ∧
    (∀ (g : G) (v : V), ((ρV g).baseChange k) ((1 : k) ⊗ₜ[R] v) = (1 : k) ⊗ₜ[R] (ρV g v)) ∧
    (Function.Injective (algebraMap R k) → Function.Injective (fun v : V => (1 : k) ⊗ₜ[R] v)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq.solution
