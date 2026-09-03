import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.epsteinPlus_globalPointsGL_mul
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ)]
    (du : MeasureTheory.Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (NumberField.RingOfIntegers ℚ) ℚ))
    (Φ : (Fin 3 → NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) → ℂ) (σ : ℝ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    epsteinPlus du Φ σ (globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g) = epsteinPlus du Φ σ g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_epsteinPlus_globalPointsGL_mul.solution
