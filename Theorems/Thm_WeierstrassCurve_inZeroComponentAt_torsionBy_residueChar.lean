import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.inZeroComponentAt_torsionBy_residueChar
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (t : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point q)
    (ht : W.InZeroComponentAt A (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) :
    (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 ∨
      ∃ (x y : AlgebraicClosure ℚ) (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
        (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = .some x y h ∧ x ∉ A := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar.solution
