import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly

set_option autoImplicit false

open Polynomial

theorem ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (𝒪 : ValuationSubring F) [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]
    (c : L) (hc : IsIntegral 𝒪 c)
    (hgen : IntermediateField.adjoin F ({c} : Set L) = ⊤)
    (hdisc : ∃ u : 𝒪ˣ, algebraMap 𝒪 F u = Algebra.norm F (aeval c (derivative (minpoly F c))))
    (z : L) (hz : IsIntegral 𝒪 z) :
    z ∈ Algebra.adjoin 𝒪 ({c} : Set L) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.solution
