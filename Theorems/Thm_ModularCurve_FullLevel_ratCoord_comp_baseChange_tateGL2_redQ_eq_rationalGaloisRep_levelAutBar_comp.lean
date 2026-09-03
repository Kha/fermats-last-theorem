import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (hGL : GL2Laws q M')
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (hΨ : ∀ (γ : SL(2, ℤ)) (x : TateModule lam (Jac q M')) (ζ : Idx q),
      Ψ (tateEnd q M' lam (slJac q M' γ) x) ζ =
        JH.tateEnd (q ^ 2 * M') (levelH q M') lam (levelOp q M' ζ γ⁻¹) (Ψ x ζ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (ζ : Idx q) :
    ratCoord q M' lam Ψ ζ ∘ₗ (tateGL2 q M' lam (redQ q γ)).baseChange ℚ_[lam] =
      ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (AlgebraicCurve.SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) ∘ₗ ratCoord q M' lam Ψ ζ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_redQ_eq_rationalGaloisRep_levelAutBar_comp.solution
