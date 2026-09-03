import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_mul_gauge3_rpow_div_sub_one

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_le_mul_gauge3_rpow_div_sub_one
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ))
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (M R₀ : ℝ) (hR₀ : 0 ≤ R₀) (N : ℕ) (hN : 0 < N)
    (hM : ∀ x, ‖Φ x‖ ≤ M)
    (hsupp : ∀ x, Φ x ≠ 0 → ∀ i, ‖(x i).1 Rat.infinitePlace‖ ≤ R₀)
    (hfin : ∀ x, Φ x ≠ 0 → ∀ (i : Fin 3) (w : HeightOneSpectrum (𝓞 ℚ)),
      ((N : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) * (x i).2) w ∈ w.adicCompletionIntegers ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (σ : ℝ) (hσ : 1 < σ) :
    epsteinPlus du Φ σ g ≤
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ *
          (9 * M * (R₀ * N * gauge3 ℚ g) ^ (3 * σ) / (σ - 1))) * du Set.univ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_le_mul_gauge3_rpow_div_sub_one.solution
