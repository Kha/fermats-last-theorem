import Definitions.Def_FLTPrelim_ModularRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsIntegralModelOf_exists_linearEquiv_torsionBy

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.IsIntegralModelOf.exists_linearEquiv_torsionBy {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} (h : W.IsIntegralModelOf E) (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point n, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : Submodule.torsionBy ℤ (E⁄(AlgebraicClosure ℚ)).Point n), φ (σ • x) = σ • φ x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsIntegralModelOf_exists_linearEquiv_torsionBy.solution
