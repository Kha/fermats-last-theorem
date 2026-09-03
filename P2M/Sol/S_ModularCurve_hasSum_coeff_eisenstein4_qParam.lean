import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import P2M.Util
namespace P2MW.S_ModularCurve_hasSum_coeff_eisenstein4_qParam
set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem solution (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion (f := ⇑ModularForm.E₄) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄) τ
  rw [ModularCurve.qExpansion_E4_eq_map_eisenstein4] at h
  simpa only [PowerSeries.coeff_map, smul_eq_mul, eq_intCast] using h
