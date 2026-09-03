import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf

open scoped NNReal
open scoped WeierstrassCurve.Affine in
open WeierstrassCurve WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf
    (E : WeierstrassCurve ℚ) {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    (p : ℕ) [Fact p.Prime] :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    ∃ ψ : Submodule.torsionBy ℤ ((E.map (algebraMap ℚ ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p ≃+
          Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ_[p]))⁄(AlgebraicClosure ℚ_[p])).Point p,
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) P,
        ψ (σ • P) = σ • ψ P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_torsionBy_padicAlgClosure_of_isIntegralModelOf.solution
