import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hΔ : W.Δ ≠ 0) (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) :
    ((W.map (Int.castRingHom ℚ)).tateModuleRep p hcard).IsUnipotentOnInertiaAt q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction.solution
