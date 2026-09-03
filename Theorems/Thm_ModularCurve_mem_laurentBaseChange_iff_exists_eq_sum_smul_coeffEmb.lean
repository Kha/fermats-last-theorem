import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb

set_option autoImplicit false

open scoped BigOperators

theorem ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
    (L : Type) [Field L] [CharZero L]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ L)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (f : LaurentSeries L) :
    f ∈ ModularCurve.laurentBaseChange L F₀ ↔
      ∃ h : ι → ↥F₀, f = ∑ i, (b i) • ModularCurve.coeffEmb L ((h i : ↥F₀) : LaurentSeries ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb.solution
