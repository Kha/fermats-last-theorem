import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed

set_option autoImplicit false

theorem LanglandsTunnell.exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hagree : AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite
      (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld H) Φ)
      ((LanglandsTunnell.P2.liftTraceSeed e H).map AutomorphicForm.iotaZsqrtdNegTwo)) :
    ∃ C : ℝ, ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), ‖Φ.a p‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_norm_a_le_of_formalBaseChange_agrees_liftTraceSeed.solution
