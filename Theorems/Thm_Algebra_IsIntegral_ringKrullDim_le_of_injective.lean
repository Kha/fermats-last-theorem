import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsIntegral_ringKrullDim_le_of_injective

set_option autoImplicit false

theorem Algebra.IsIntegral.ringKrullDim_le_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsIntegral_ringKrullDim_le_of_injective.solution
