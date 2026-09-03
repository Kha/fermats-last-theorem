import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) {n : ℕ} (hn : ¬ q ∣ n) {x y : AlgebraicClosure ℚ} (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y) (hP : n • Point.some x y h = 0) : x ∈ A := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_valuationSubring_of_nsmul_eq_zero_of_liesOverPrime.solution
