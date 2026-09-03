import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase

theorem AlgebraicCurve.GluedPic0.nodeUnit_eq_zero_iff_of_constantsAreBase
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F)) (w : ↥S → Additive Kˣ) :
    nodeUnit S w = 0 ↔ ∃ c : Kˣ, w = fun _ => Additive.ofMul c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase.solution
