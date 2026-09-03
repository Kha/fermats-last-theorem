import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Complex
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import P2M.Util
import P2M.Sol.S_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
attribute [-simp] MeasureTheory.L2.kernelIntegralLM_apply

set_option autoImplicit false

theorem ContinuousMap.exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (f : C(G, ℂ)) (hf : f ≠ 0) (R : Set (G →₀ ℂ))
    (hR : ∀ r ∈ R, ∀ x : G, (r.sum fun g c => c * f (x * g)) = 0) :
    ∃ χ : G →* ℂˣ, Continuous χ ∧ ∀ r ∈ R, (r.sum fun g c => c * ((χ g : ℂˣ) : ℂ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ContinuousMap_exists_continuous_monoidHom_forall_sum_eq_zero_of_compactSpace.solution
