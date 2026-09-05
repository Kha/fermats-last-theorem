module

public import Definitions.Def_ModularCurve_ModularUnit
public import Definitions.Def_ModularForm_HeckeOperator
public import Mathlib.NumberTheory.ModularForms.Discriminant
import P2M.Sol.S_ModularCurve_hasSum_modularUnitSeries_qParam
import P2M.Sol.S_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
import P2M.Sol.S_ModularCurve_hasSum_modularUnitSeries_inv_qParam
import P2M.Sol.S_ModularCurve_hasSum_smul_modularUnitSeries_qParam
import P2M.Sol.S_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import P2M.Sol.S_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant
import P2M.Util

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ) := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact ModularCurve.isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => ModularCurve.hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)
end S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries
end P2MW

public section
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.isIntegral_adjoin_jq_modularUnitSeries (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries.solution
end
