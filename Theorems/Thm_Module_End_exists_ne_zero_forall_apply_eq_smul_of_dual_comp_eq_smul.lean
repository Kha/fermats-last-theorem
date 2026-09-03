import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul

set_option autoImplicit false

theorem Module.End.exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul
    {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    {R : Type*} [CommRing R] (T : R →+* Module.End K M) (a : R →+* K)
    (μ : Module.Dual K M) (hμ : μ ≠ 0) (hco : ∀ r : R, μ ∘ₗ (T r : M →ₗ[K] M) = a r • μ) :
    ∃ m : M, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul.solution
