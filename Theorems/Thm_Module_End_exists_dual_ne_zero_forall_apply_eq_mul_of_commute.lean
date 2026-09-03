import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_dual_ne_zero_forall_apply_eq_mul_of_commute

set_option autoImplicit false

theorem Module.End.exists_dual_ne_zero_forall_apply_eq_mul_of_commute
    {K : Type*} [Field K] [IsAlgClosed K]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Nontrivial W]
    {ι : Type*} (T : ι → Module.End K W) (hT : ∀ i j : ι, Commute (T i) (T j)) :
    ∃ (μ : W →ₗ[K] K) (c : ι → K), μ ≠ 0 ∧ ∀ (i : ι) (w : W), μ (T i w) = c i * μ w := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_dual_ne_zero_forall_apply_eq_mul_of_commute.solution
