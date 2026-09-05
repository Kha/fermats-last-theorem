module

public import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv

@[expose] public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.isIntegral_adjoin_jq_modularUnitSeries_inv (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv.solution
