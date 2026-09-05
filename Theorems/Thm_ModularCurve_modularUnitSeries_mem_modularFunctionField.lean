module

public import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionField

@[expose] public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.modularUnitSeries_mem_modularFunctionField (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionField.solution
