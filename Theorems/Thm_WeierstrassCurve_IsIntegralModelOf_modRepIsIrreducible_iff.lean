import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsIntegralModelOf_modRepIsIrreducible_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.IsIntegralModelOf.modRepIsIrreducible_iff {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} (h : W.IsIntegralModelOf E) (n : ℕ) : W.ModRepIsIrreducible n ↔ Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E n := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsIntegralModelOf_modRepIsIrreducible_iff.solution
