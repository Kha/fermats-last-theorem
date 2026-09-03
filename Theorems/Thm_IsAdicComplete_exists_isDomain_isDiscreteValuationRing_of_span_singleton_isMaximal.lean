import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal

set_option autoImplicit false

universe u

theorem IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
    {𝓞 : Type u} [CommRing 𝓞] (ϖ : 𝓞) (hϖ : ϖ ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible ϖ ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {ϖ} := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal.solution
