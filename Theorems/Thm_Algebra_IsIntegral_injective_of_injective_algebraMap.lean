import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsIntegral_injective_of_injective_algebraMap

set_option autoImplicit false

theorem Algebra.IsIntegral.injective_of_injective_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsDomain B] [IsDomain C]
    [Algebra A B] [Algebra A C] [Algebra.IsIntegral A B]
    (hinj : Function.Injective (algebraMap A C)) (φ : B →ₐ[A] C) :
    Function.Injective φ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsIntegral_injective_of_injective_algebraMap.solution
