import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly

set_option autoImplicit false

theorem ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_separable_minpoly
    {κ F L : Type*} [Field κ] [Field F] [Field L] [Algebra κ F] [Algebra F L] [Algebra κ L] [IsScalarTower κ F L]
    (𝒪 : ValuationSubring F) [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]
    (hκ : ∀ a : κ, algebraMap κ F a ∈ 𝒪)
    (c : L) (hc : IsIntegral κ c) (hsep : (minpoly κ c).Separable)
    (hgen : IntermediateField.adjoin F ({c} : Set L) = ⊤)
    (z : L) (hz : IsIntegral 𝒪 z) :
    z ∈ Algebra.adjoin 𝒪 ({c} : Set L) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly.solution
