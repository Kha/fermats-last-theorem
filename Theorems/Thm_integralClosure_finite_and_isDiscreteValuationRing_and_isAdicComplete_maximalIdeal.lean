import Mathlib
import P2M.Util
import P2M.Sol.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal

theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') := by p2m_exact_reverting @_root_.P2MW.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal.solution
