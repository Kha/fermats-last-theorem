import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exact_dualMap_of_exact

set_option autoImplicit false
theorem LinearMap.exact_dualMap_of_exact {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exact_dualMap_of_exact.solution
