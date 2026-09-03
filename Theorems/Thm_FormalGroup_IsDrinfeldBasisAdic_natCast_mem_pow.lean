import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_natCast_mem_pow

set_option autoImplicit false

p2m_open "FormalGroup~coeff_one_nthSeries IsLocalRing"

theorem FormalGroup.IsDrinfeldBasisAdic.natCast_mem_pow
    {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T) (q : ℕ)
    (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    (q : T) ∈ I ^ (q * q - 1) := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_natCast_mem_pow.solution
