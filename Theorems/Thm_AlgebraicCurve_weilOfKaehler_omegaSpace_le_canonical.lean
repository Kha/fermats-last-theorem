import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_weilOfKaehler_omegaSpace_le_canonical

namespace AlgebraicCurve

theorem weilOfKaehler_omegaSpace_le_canonical {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehler K F hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilOfKaehler_omegaSpace_le_canonical.solution
