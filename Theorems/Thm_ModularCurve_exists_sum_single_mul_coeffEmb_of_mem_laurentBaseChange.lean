import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange

set_option autoImplicit false

theorem ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (y : LaurentSeries L) (hy : y ∈ ModularCurve.laurentBaseChange L F₀) :
    ∃ (n : ℕ) (c : Fin n → L) (f : Fin n → LaurentSeries ℚ), (∀ i, f i ∈ F₀) ∧
      y = ∑ i, HahnSeries.single 0 (c i) * ModularCurve.coeffEmb L (f i) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange.solution
