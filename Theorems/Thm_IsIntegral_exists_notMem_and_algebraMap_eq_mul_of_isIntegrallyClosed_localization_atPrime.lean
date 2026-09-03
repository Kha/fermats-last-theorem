import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime

set_option autoImplicit false

theorem IsIntegral.exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime
    {B F : Type*} [CommRing B] [CommRing F] [Algebra B F]
    (M : Submonoid B) (hM : M ≤ nonZeroDivisors B) [IsLocalization M F]
    (𝔮 : Ideal B) [𝔮.IsPrime] [IsDomain (Localization.AtPrime 𝔮)] [IsIntegrallyClosed (Localization.AtPrime 𝔮)]
    (t : F) (ht : IsIntegral B t) :
    ∃ s : B, s ∉ 𝔮 ∧ ∃ c : B, algebraMap B F c = algebraMap B F s * t := by p2m_exact_reverting @_root_.P2MW.S_IsIntegral_exists_notMem_and_algebraMap_eq_mul_of_isIntegrallyClosed_localization_atPrime.solution
