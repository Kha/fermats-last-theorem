import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral
    (M : ℕ) [NeZero M] (k : ℕ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (pg : PowerSeries ℤ) (hg : ModularCurve.IsIntegralQExp g pg)
    (hint : ∀ (γ : SL(2, ℤ)) (n : ℕ), IsIntegral ℤ
      ((UpperHalfPlane.qExpansion (M : ℝ) ((⇑g : UpperHalfPlane → ℂ) ∣[(k : ℤ)] (γ : GL (Fin 2) ℝ))).coeff n)) :
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) /
        ModularCurve.intSeriesC ℚ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k)) ∧
    (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) ModularCurve.jq⁻¹).IsIntegralElem
      (ModularCurve.intSeriesC ℚ (pg ^ 12) / ModularCurve.intSeriesC ℚ (ModularCurve.eisenstein4 ^ (3 * k))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegralElem_div_delta_pow_and_div_eisenstein4_pow_of_forall_qExpansion_slash_isIntegral.solution
