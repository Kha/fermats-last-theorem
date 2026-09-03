import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hK : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ)
    (hW0 : W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) ≠ 0) :
    x ∈ v.adicCompletionIntegers ℚ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnitGL2_mul_lowerUnipotent21_ne_zero.solution
