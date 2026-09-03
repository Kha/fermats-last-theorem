import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∃ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg h : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp f pf ∧ ModularCurve.IsIntegralQExp g pg ∧ pg ≠ 0 ∧ pf = pg * h ∧
      PowerSeries.constantCoeff h = 0 ∧
      (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) (ModularCurve.jq)⁻¹).IsIntegralElem
        (ModularCurve.intSeriesC ℚ h) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M'),
        ∃ (f₁ g₁ : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
          (pf₁ pg₁ h₁ : PowerSeries ℤ) (c : ℂ),
          c ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ pf₁ ∧ ModularCurve.IsIntegralQExp g₁ pg₁ ∧
          (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∧
          (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∧
          pg₁ ≠ 0 ∧ pf₁ = pg₁ * h₁ ∧
          (CohCarrier.gamma0Units (q ^ 2 * M') γ ∉
              ModularCurve.FullLevel.levelH q M' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M'))ˣ) →
            IsUnit (PowerSeries.constantCoeff h₁)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit.solution
