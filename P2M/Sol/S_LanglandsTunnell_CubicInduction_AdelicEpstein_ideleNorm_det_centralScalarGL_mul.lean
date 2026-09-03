import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_ideleNorm_det_centralScalarGL_mul

set_option autoImplicit false

noncomputable section

open NumberField LanglandsTunnell.CubicInduction

namespace CentralNorm

private theorem ideleNorm_pow (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℕ) :
    TateGlobal.ideleNorm ℚ (z ^ n) = TateGlobal.ideleNorm ℚ z ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have h := TateGlobal.ideleNorm_mul (F := ℚ) (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) 1
    rw [mul_one] at h
    have hpos := TateGlobal.ideleNorm_pos (F := ℚ) (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    exact mul_left_cancel₀ hpos.ne' (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [pow_succ, TateGlobal.ideleNorm_mul, ih, pow_succ]

private theorem det_centralScalarGL (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z) = z ^ 3 := by
  unfold centralScalarGL
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

end CentralNorm

open LanglandsTunnell LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein

theorem solution
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) (g : AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (NumberField.RingOfIntegers ℚ) ℚ z * g))
      = NumberField.TateGlobal.ideleNorm ℚ z ^ 3
          * NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, CentralNorm.det_centralScalarGL, CentralNorm.ideleNorm_pow]
