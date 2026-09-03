import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

theorem LanglandsTunnell.exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))),
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L),
        Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥ → IsArithFrobAt (𝓞 ℚ) σ Q →
        orderOf (e σ) = 8 →
        ∀ w : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e))), w ∉ S' → w.under (𝓞 ℚ) = v →
          (P2.liftTraceSeed e (quatH e)).a w = 0 ∧ (P2.liftTraceSeed e (quatH e)).b w = 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_finset_liftTraceSeed_quatH_a_eq_zero_of_orderOf_eq_eight.solution
