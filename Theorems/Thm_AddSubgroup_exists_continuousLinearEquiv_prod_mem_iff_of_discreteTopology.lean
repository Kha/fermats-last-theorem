import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology

set_option autoImplicit false

theorem AddSubgroup.exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ (a b : ℕ) (T : ((Fin a → ℝ) × (Fin b → ℝ)) ≃L[ℝ] V),
      ∀ x : V, x ∈ L ↔ ∃ k : Fin a → ℤ, T (fun i => (k i : ℝ), 0) = x := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_exists_continuousLinearEquiv_prod_mem_iff_of_discreteTopology.solution
