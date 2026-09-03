import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_traceDiff_apply

theorem AlgebraicCurve.traceDiff_apply (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (y : F') (ω : Ω[F⁄K]) : traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_traceDiff_apply.solution
