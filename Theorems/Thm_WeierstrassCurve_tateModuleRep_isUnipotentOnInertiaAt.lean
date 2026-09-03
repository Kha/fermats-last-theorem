import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt (W : WeierstrassCurve ℚ) (p : ℕ)
    [Fact p.Prime]
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hgeom : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ n : ℕ,
        ∀ P ∈ Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ),
          σ • (σ • P - P) = σ • P - P) :
    (W.tateModuleRep p hcard).IsUnipotentOnInertiaAt q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt.solution
