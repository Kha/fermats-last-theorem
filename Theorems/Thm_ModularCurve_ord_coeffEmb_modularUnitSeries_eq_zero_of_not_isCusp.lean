import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp (N : ℕ) [NeZero N]
    (δ : ℕ) [NeZero δ] (hδ : δ ∣ N) (hmem : modularUnitSeries δ ∈ modularFunctionFieldFull N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hv : ¬ IsCusp (CharPModel.jBar N) v) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries δ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ : modularFunctionFieldBar N) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp.solution
