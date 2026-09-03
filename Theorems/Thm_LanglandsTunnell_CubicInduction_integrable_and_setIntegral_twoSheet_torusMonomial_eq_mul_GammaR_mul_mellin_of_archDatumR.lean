import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell~exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin LanglandsTunnell.CubicInduction MeasureTheory"

theorem LanglandsTunnell.CubicInduction.integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
    (a : ℚ) (ha : a ≠ 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₃ : ℂ) (a₃ : ZMod 2) (n i j l : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + ε * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) *
            (ArchR.quasiChar (u₃ + 2) a₃ (q.2.1 * q.2.2)⁻¹ * (((q.2.2 ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ q.2.2 *
              (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + (q.2.2 ^ 2)⁻¹ + (a : ℝ) ^ 2 * q.2.2 ^ 2 + (a : ℝ) ^ 2 * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) *
              (D.W (ArchR.diagOne ((a : ℝ) * q.1 * q.2.1 / q.2.2)) + ε * D.W (ArchR.diagOne (-((a : ℝ) * q.1 * q.2.1 / q.2.2)))) *
              ((((q.2.1⁻¹) ^ i * (q.2.2⁻¹) ^ j * ((a : ℝ) * q.1 * q.2.1) ^ l : ℝ)) : ℂ)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s + (l : ℂ) - 1) ∧
      ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
            ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
              (D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) + ε * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂)))) *
              ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ) =
        (a : ℂ) ^ l * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (i : ℂ)) * mellin H (s + (l : ℂ) - 1)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR.solution
