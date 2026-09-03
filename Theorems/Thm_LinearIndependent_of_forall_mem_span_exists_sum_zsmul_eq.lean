import Mathlib
import P2M.Util
import P2M.Sol.S_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq

set_option autoImplicit false

theorem LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k : ℕ} (b₀ : Module.Basis (Fin k) ℝ V) (v : Fin k → V)
    (hgen : ∀ x ∈ Submodule.span ℤ (Set.range b₀), ∃ n : Fin k → ℤ, (∑ i, n i • v i) = x) :
    LinearIndependent ℝ v := by p2m_exact_reverting @_root_.P2MW.S_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq.solution
