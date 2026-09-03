import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem

namespace AlgebraicCurve

theorem weilKaehlerAgree_of_residueTheorem {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasSeparableResidue K F] [Nonempty (Place K F)]
    (hRT : ResidueTheorem K F) : WeilKaehlerAgree K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_weilKaehlerAgree_of_residueTheorem.solution
