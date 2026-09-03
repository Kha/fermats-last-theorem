import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker

set_option autoImplicit false
open Module
theorem LinearMap.finrank_ker_dualMap_eq_finrank_ker
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker.solution
