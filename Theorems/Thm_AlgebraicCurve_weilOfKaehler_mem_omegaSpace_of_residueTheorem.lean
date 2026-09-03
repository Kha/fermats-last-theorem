import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem

namespace AlgebraicCurve

theorem weilOfKaehler_mem_omegaSpace_of_residueTheorem {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.solution
