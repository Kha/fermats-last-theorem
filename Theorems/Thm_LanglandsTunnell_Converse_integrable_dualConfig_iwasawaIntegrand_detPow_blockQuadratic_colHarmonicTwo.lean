import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (ha : a ≠ 0) (u : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) :
    Integrable (fun q : ℝ × ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (q.1 ^ 2 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2) + 1 / q.2.1 ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |q.2.1 * q.2.2| : ℝ)) : ℂ) *
            (((q.2.1⁻¹ : ℝ) : ℂ) ^ 2 *
              ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ))) ^ δ *
                  ((a₂⁻¹ : ℂ) ^ 2 * ((((q.1 ^ 2 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 : ℝ)) : ℂ) - Complex.I * (((2 * q.1 / (q.2.1 * q.2.2) : ℝ)) : ℂ)) +
                    (a : ℂ) ^ 2 * (a₁ : ℂ) ^ 2 * (((q.2.2 ^ 2 : ℝ)) : ℂ)) +
                (δ : ℂ) / (Real.pi : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ)) * (1 + Complex.I * (((q.1 * q.2.2 / q.2.1 : ℝ)) : ℂ)))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * q.2.2 ^ 2)) : ℂ)) *
          (ArchR.quasiChar u a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * q.1) * (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * q.2.1 / q.2.2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo.solution
