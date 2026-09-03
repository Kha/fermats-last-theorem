import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal

universe u

theorem IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] :
    ∃ (_ : IsDomain 𝓞) (_ : IsDiscreteValuationRing 𝓞),
      Irreducible (p : 𝓞) ∧ IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_natCast_isMaximal.solution
