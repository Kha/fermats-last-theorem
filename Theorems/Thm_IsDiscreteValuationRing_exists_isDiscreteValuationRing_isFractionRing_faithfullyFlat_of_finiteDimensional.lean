import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra 𝒪 K'] [IsScalarTower 𝒪 K K'] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Algebra 𝒪' K') (_ : IsScalarTower 𝒪 𝒪' K') (_ : IsFractionRing 𝒪' K')
      (_ : IsLocalHom (algebraMap 𝒪 𝒪')), Module.FaithfullyFlat 𝒪 𝒪' := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_isDiscreteValuationRing_isFractionRing_faithfullyFlat_of_finiteDimensional.solution
