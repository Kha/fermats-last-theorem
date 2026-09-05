module

public import Definitions.Def_ModularCurve_ModularUnit
public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries

@[expose] public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.coe_frickeInvolutionFull_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hmem : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionFieldFull ℓ) : ((ModularCurve.frickeInvolutionFull ℓ ⟨ModularCurve.modularUnitSeries ℓ, hmem⟩ : ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries.solution
