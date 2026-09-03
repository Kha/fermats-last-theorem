import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair
import P2M.Util
import P2M.Sol.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_central_isUnit

open scoped Pointwise
open LocalGL2 HeckePair
theorem LocalGL2.heckeIndicator_diagPi_mul_localRepInf_central_isUnit
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)
    {R₀ : Type*} [CommRing R₀]
    (hfin : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    (∀ f : HeckeAlgebra (integralSubgroup R K) R₀,
        heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin * f
          = f * heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin) ∧
      IsUnit (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin :
        HeckeAlgebra (integralSubgroup R K) R₀) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_central_isUnit.solution
