import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Theorems.Thm_ModularCurve_JZero_eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one
import Theorems.Thm_ModularCurve_JZero_heightForm_single
import Theorems.Thm_ModularCurve_JZero_baseMass_add_single_cuspInftyBar
import Theorems.Thm_ModularCurve_JZero_baseMass_single
import P2M.Util
namespace P2MW.S_ModularCurve_JZero_heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace P2MM1
open ModularCurve.JZero

theorem heightForm_zero (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) :
    JZero.heightForm N s 0 = 0 := by
  classical
  simp [JZero.heightForm, AlgebraicCurve.heightForm, heightFormAux, Finsupp.sum_zero_index]

theorem baseMass_zero (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) :
    baseMass N s 0 = 0 := by
  classical
  simp [baseMass, Finsupp.sum_zero_index]

end P2MM1

open ModularCurve.JZero P2MM1 in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hm : offBaseMass N D ≤ 1) :
    heightForm N s D = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * baseMass N s D := by
  rcases ModularCurve.JZero.eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one N D hD hm with h | ⟨v, hv, h⟩
  ·
    rw [h, ← zero_add (Finsupp.single (cuspInftyBar N) (D (cuspInftyBar N))),
      JZero.heightForm_add_single_cuspInftyBar, baseMass_add_single_cuspInftyBar, heightForm_zero, baseMass_zero,
      mul_zero]
  ·
    rw [h, JZero.heightForm_add_single_cuspInftyBar, baseMass_add_single_cuspInftyBar,
      JZero.heightForm_single N s hv 1, baseMass_single N s hv 1]
    push_cast
    ring
