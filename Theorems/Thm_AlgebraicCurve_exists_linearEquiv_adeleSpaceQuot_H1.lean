import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_linearEquiv_adeleSpaceQuot_H1

namespace AlgebraicCurve
theorem exists_linearEquiv_adeleSpaceQuot_H1 {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] (D : Divisor K F) :
    ∃ e : (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ≃ₗ[K] H1 D,
      ∀ (a : ↥(adeleSpace K F)) (ha : (a : Place K F → F) ∈ repartitions K F),
        e (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨(a : Place K F → F), ha⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_linearEquiv_adeleSpaceQuot_H1.solution
end AlgebraicCurve
