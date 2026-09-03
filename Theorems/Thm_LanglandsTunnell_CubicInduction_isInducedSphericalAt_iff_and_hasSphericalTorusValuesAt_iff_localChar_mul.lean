import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ v)
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w)
    (W : LocalGL3 v → ℂ) :
    (IsInducedSphericalAt c v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ↔
      IsInducedSphericalAt c' v (localMaximalCompact3 (𝓞 ℚ) ℚ v)
        (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) ∧
    (HasSphericalTorusValuesAt c v W ↔
      HasSphericalTorusValuesAt c' v (fun g => (localChar χ v (Matrix.GeneralLinearGroup.det g) : ℂ) * W g)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isInducedSphericalAt_iff_and_hasSphericalTorusValuesAt_iff_localChar_mul.solution
