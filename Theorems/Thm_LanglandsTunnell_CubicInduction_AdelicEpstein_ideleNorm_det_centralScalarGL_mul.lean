import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.AdelicEpstein.ideleNorm_det_centralScalarGL_mul
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (NumberField.RingOfIntegers ℚ) ℚ z * g))
      = NumberField.TateGlobal.ideleNorm ℚ z ^ 3
          * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul.solution
