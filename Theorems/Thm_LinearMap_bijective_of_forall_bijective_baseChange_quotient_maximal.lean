import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.bijective_of_forall_bijective_baseChange_quotient_maximal
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N] (f : M →ₗ[R] N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
    Function.Bijective f := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal.solution
