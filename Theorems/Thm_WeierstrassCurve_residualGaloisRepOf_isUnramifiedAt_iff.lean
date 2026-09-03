import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ W p q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_residualGaloisRepOf_isUnramifiedAt_iff.solution
