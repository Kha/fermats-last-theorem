import Mathlib
import P2M.Util
import P2M.Sol.S_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent

set_option autoImplicit false

theorem IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
    {X : Type*} [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {k : ℕ} {S : Set X} (hS : IsPreconnected S)
    (v : Fin k → X → V) (hv : ∀ i, ContinuousOn (v i) S)
    (hlin : ∀ z ∈ S, LinearIndependent ℝ (fun i => v i z))
    (x : X → V) (hx : ContinuousOn x S)
    (hmem : ∀ z ∈ S, ∃ n : Fin k → ℤ, x z = ∑ i, n i • v i z) :
    ∃ n : Fin k → ℤ, ∀ z ∈ S, x z = ∑ i, n i • v i z := by p2m_exact_reverting @_root_.P2MW.S_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent.solution
