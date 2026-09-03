import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_linearEquiv_tateModule_jac_pi_tateGal_slJac_diagJac

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.exists_linearEquiv_tateModule_jac_pi_tateGal_slJac_diagJac
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] :
    ∃ Ψ : TateModule lam (Jac q M') ≃ₗ[ℤ_[lam]] (Idx q → TateModule lam (jacComp q M')),
      (∀ (x : TateModule lam (Jac q M')) (ζ : Idx q) (n : ℕ),
        ((Ψ x ζ : TateModule lam (jacComp q M')) : ℕ → jacComp q M') n =
          (((x : TateModule lam (Jac q M')) : ℕ → Jac q M') n).eval ζ) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
        Ψ (tateGal q M' lam σ x) ζ =
          JH.tateGaloisRep (q ^ 2 * M') (levelH q M') lam σ (Ψ x (σ⁻¹ • ζ))) ∧
      (∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
        Ψ (tateEnd q M' lam (slJac q M' γ) x) ζ =
          JH.tateEnd (q ^ 2 * M') (levelH q M') lam (levelOp q M' ζ γ⁻¹) (Ψ x ζ)) ∧
      (∀ (d : (ZMod q)ˣ) (x : TateModule lam (Jac q M')) (ζ : Idx q),
        Ψ (tateEnd q M' lam (diagJac q M' d) x) ζ = Ψ x (ζ.pow d⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_linearEquiv_tateModule_jac_pi_tateGal_slJac_diagJac.solution
