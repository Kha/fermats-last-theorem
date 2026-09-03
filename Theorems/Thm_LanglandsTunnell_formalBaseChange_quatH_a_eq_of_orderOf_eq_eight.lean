import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_formalBaseChange_quatH_a_eq_of_orderOf_eq_eight

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

theorem LanglandsTunnell.formalBaseChange_quatH_a_eq_of_orderOf_eq_eight
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (Φ : HeckeEigensystem ℚ ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L)
    (hQ : Q.IsMaximal) (hQv : Q.under (𝓞 ℚ) = v.asIdeal) (hunr : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (hσ : IsArithFrobAt (𝓞 ℚ) σ Q) (h8 : orderOf (e σ) = 8)
    (w : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))) (hw : w.under (𝓞 ℚ) = v) :
    (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).a w
        = Φ.a v ^ 2 - 2 * Φ.b v ∧
      (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e)) (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).b w
        = Φ.b v ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_formalBaseChange_quatH_a_eq_of_orderOf_eq_eight.solution
