import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (e₁ e₂ e₃ : ℂ) (he₃ : e₃ ≠ 0)
    (hcen : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (h1 : W 1 = 1)
    (htv₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (htv₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (dualWhittakerFn3 W) ∧
    IsGL3PsiWhittakerFn ψv⁻¹ (dualWhittakerFn3 W) ∧
    dualWhittakerFn3 W 1 = 1 ∧
    (∀ g : LocalGL3 v, dualWhittakerFn3 W (centralGen v * g) = e₃⁻¹ * dualWhittakerFn3 W g) ∧
    (∀ n : ℕ, dualWhittakerFn3 W (iotaTorusLocal v n) =
      (cNormQ v)⁻¹ ^ n * sphericalTorusValue (e₂ * e₃⁻¹) (e₁ * e₃⁻¹) e₃⁻¹ n) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_dualWhittakerFn3_spherical_and_iotaTorusLocal_eq_of_torusValues.solution
