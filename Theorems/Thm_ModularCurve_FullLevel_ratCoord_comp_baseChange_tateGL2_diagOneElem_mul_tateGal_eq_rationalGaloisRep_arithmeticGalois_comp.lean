import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_diagOneElem_mul_tateGal_eq_rationalGaloisRep_arithmeticGalois_comp

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.ratCoord_comp_baseChange_tateGL2_diagOneElem_mul_tateGal_eq_rationalGaloisRep_arithmeticGalois_comp
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]
    (hGL : GL2Laws q M')
    (Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')))
    (hΨgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
      Ψ (tateGal q M' lam σ x) ζ =
        JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam σ (Ψ x (σ⁻¹ • ζ)))
    (hΨdiag : ∀ (d : (ZMod q)ˣ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
      Ψ (tateEnd q M' lam (diagJac q M' d) x) ζ = Ψ x (ζ.pow d⁻¹))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (e : (ZMod q)ˣ)
    (hlab : ∀ ζ : Idx q, σ • ζ = ζ.pow e⁻¹) (ζ : Idx q) :
    ratCoord q M' lam Ψ ζ ∘ₗ (tateGL2 q M' lam (diagOneElem q e) * tateGal q M' lam σ).baseChange ℚ_[lam] =
      ModularCurve.rationalGaloisRep lam (AlgebraicCurve.Pic0 (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (levelH q M')) σ) ∘ₗ
        ratCoord q M' lam Ψ ζ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_ratCoord_comp_baseChange_tateGL2_diagOneElem_mul_tateGal_eq_rationalGaloisRep_arithmeticGalois_comp.solution
