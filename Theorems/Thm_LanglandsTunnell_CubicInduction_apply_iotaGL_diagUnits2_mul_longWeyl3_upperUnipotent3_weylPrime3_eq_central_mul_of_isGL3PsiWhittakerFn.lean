import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnits2_mul_longWeyl3_upperUnipotent3_weylPrime3_eq_central_mul_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnits2_mul_longWeyl3_upperUnipotent3_weylPrime3_eq_central_mul_of_isGL3PsiWhittakerFn
    {K : Type*} [Field K] (ψ : AddChar K ℂ) (W : GL (Fin 3) K → ℂ) (hW : IsGL3PsiWhittakerFn ψ W)
    (ω : Kˣ →* ℂˣ)
    (hω : ∀ (z : Kˣ) (g : GL (Fin 3) K), W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (t a u : Kˣ) :
    W (iotaGL (diagUnits2 (t * a) a) * (longWeyl3 * upperUnipotent3 0 0 (u : K) * weylPrime3)) =
      ((ω u : ℂˣ) : ℂ) *
        W (iotaGL (diagUnits2 (-(t * u⁻¹) * (a * u⁻¹)) (a * u⁻¹)) *
          (longWeyl3 * upperUnipotent3 0 0 ((u⁻¹ : Kˣ) : K) * longWeyl3 * weylPrime3)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnits2_mul_longWeyl3_upperUnipotent3_weylPrime3_eq_central_mul_of_isGL3PsiWhittakerFn.solution
