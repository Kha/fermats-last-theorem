module

public import Definitions.Def_ModularCurve_ModularUnit
public import Definitions.Def_ModularCurve_AtkinLehner
public import Definitions.Def_ModularForm_HeckeOperator
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
public import Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
public import Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
public import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hmem : ModularCurve.modularUnitSeries ℓ ∈ ModularCurve.modularFunctionFieldFull ℓ) : ((ModularCurve.frickeInvolutionFull ℓ ⟨ModularCurve.modularUnitSeries ℓ, hmem⟩ : ModularCurve.modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = (ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹ := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  exact ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ) ((ℓ : ℚ) ^ 12 • (ModularCurve.modularUnitSeries ℓ)⁻¹)
    (fun τ => ModularForm.discriminant τ
      / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))
    (fun τ => ModularCurve.hasSum_modularUnitSeries_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_inv_qParam ℓ τ)
    (fun γ hγ τ => ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ) hmem
