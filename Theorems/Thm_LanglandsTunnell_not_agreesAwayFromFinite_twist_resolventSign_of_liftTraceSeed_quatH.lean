import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false
open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell

theorem LanglandsTunnell.not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : HeckeEigensystem ℚ ℂ)
    (h₆seed : (formalBaseChange ↥(fixFld (detKer e)) ↥(fixFld (quatH e))
          (formalBaseChange ℚ ↥(fixFld (detKer e)) Φ)).AgreesAwayFromFinite
        ((P2.liftTraceSeed e (quatH e)).map iotaZsqrtdNegTwo))
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)

    (hdet : ∀ v ∉ S₀, ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal →
        IsArithFrobAt (𝓞 ℚ) σ Q → (χ v = 1 ↔ σ ∈ detKer e) ∧ (χ v = -1 ↔ σ ∉ detKer e)) :
    ¬ Φ.AgreesAwayFromFinite (Φ.twist χ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_not_agreesAwayFromFinite_twist_resolventSign_of_liftTraceSeed_quatH.solution
