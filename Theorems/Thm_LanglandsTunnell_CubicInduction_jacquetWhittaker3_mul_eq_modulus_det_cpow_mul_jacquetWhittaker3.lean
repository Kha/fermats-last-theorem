import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℝ)
    (hμ : ∀ u : (v.adicCompletion ℚ)ˣ,
      ((μ u : ℂˣ) : ℂ) = ((modulus (u : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ))
    (g : LocalGL3 v) :
    jacquetWhittaker3 v (fun i => χ i * μ) Φ g =
      ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (a : ℂ) *
        jacquetWhittaker3 v χ Φ g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_mul_eq_modulus_det_cpow_mul_jacquetWhittaker3.solution
