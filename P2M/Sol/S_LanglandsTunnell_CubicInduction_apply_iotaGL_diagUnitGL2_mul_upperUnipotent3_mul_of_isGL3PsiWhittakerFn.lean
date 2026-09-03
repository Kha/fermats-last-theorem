import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Mathlib
import P2M.Util
namespace P2MW.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

open LanglandsTunnell.CubicInduction

namespace Ws31
namespace TT

theorem torus_mul_upperUnipotent3 (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    (iotaGL (diagUnitGL2 u) : LocalGL3 v) * upperUnipotent3 x y z =
      upperUnipotent3 ((u : v.adicCompletion ℚ) * x) y ((u : v.adicCompletion ℚ) * z) * iotaGL (diagUnitGL2 u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, upperUnipotent3, diagUnitGL2, Matrix.mul_apply, Fin.sum_univ_three]
end Ws31.TT

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (g : LocalGL3 v) :
    W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 x 0 0 * g)) = ψv ((a : v.adicCompletion ℚ) * x) * W (iotaGL (diagUnitGL2 a) * g) := by
  rw [← mul_assoc, Ws31.TT.torus_mul_upperUnipotent3 v a x 0 0, mul_zero, mul_assoc, hW, add_zero]
