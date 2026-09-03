import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm

theorem AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (h : F') : traceDiff K F F' (h⁻¹ • KaehlerDifferential.D K F' h) = (Algebra.norm F h)⁻¹ • KaehlerDifferential.D K F (Algebra.norm F h) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm.solution
