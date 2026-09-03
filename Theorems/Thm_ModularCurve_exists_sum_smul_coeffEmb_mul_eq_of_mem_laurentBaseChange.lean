import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange

set_option autoImplicit false

open scoped BigOperators

theorem ModularCurve.exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
    (L : Type) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (x : LaurentSeries L) (hx : x ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → L) (g : ι → ↥F₀) (κ : Type) (_ : Fintype κ) (d : κ → L) (h : κ → ↥F₀),
      (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) ≠ 0 ∧
      x * (∑ j, algebraMap L (LaurentSeries L) (d j) * ModularCurve.coeffEmb L ((h j : ↥F₀) : LaurentSeries ℚ)) =
        ∑ i, algebraMap L (LaurentSeries L) (c i) * ModularCurve.coeffEmb L ((g i : ↥F₀) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange.solution
