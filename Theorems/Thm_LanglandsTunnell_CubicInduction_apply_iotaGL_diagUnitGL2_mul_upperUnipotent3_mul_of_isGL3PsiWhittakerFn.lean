import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (g : LocalGL3 v) :
    W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 x 0 0 * g)) = ψv ((a : v.adicCompletion ℚ) * x) * W (iotaGL (diagUnitGL2 a) * g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn.solution
