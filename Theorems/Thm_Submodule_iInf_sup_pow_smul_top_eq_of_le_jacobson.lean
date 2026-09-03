import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson

set_option autoImplicit false

open scoped Pointwise

theorem Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    ⨅ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = N := by p2m_exact_reverting @_root_.P2MW.S_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson.solution
