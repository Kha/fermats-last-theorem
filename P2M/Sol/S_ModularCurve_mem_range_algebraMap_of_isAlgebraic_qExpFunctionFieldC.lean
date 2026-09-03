import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic
import P2M.Util
namespace P2MW.S_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (κ : Type*) [Field κ] (Γ : Subgroup SL(2, ℤ))
    (y : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (hy : IsAlgebraic κ y) :
    y ∈ (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)).range := by
  have hy' : IsAlgebraic κ (y : LaurentSeries κ) := IntermediateField.isAlgebraic_iff.mp hy
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic (y : LaurentSeries κ) hy'
  refine ⟨c, Subtype.ext ?_⟩
  show algebraMap κ (LaurentSeries κ) c = (y : LaurentSeries κ)
  rw [hc, HahnSeries.C_apply, ModularCurve.algebraMap_laurentSeries_eq_single]
