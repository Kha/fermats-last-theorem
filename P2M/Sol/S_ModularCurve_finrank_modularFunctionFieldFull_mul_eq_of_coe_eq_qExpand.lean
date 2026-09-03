import Mathlib
import Definitions.Def_ModularCurve_X0

import Theorems.Thm_ModularCurve_finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand
import P2M.Util
namespace P2MW.S_ModularCurve_finrank_modularFunctionFieldFull_mul_eq_of_coe_eq_qExpand
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularCurve

theorem solution
    (N₀ q ℓ : ℕ) [NeZero N₀] [Fact q.Prime] [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (φ : ↥(modularFunctionFieldFull (N₀ * q)) →+* ↥(modularFunctionFieldFull (N₀ * ℓ * q)))
    (hφ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)),
      ((φ f : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) = qExpand ℚ ℓ ((f : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)) :
    @Module.finrank ↥(modularFunctionFieldFull (N₀ * q)) ↥(modularFunctionFieldFull (N₀ * ℓ * q)) _ _ φ.toAlgebra.toModule =
      (if ℓ ∣ N₀ then ℓ else ℓ + 1) := by
  have h : ℓ ∣ N₀ * q ↔ ℓ ∣ N₀ := by
    constructor
    · intro hd
      rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).mp hd with h1 | h2
      · exact h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) (Fact.out : q.Prime)).mp h2) hℓq
    · exact fun hd => dvd_mul_of_dvd_left hd q
  have key := ModularCurve.finrank_modularFunctionFieldFull_mul_prime_eq_of_coe_eq_qExpand (N₀ * q) ℓ (N₀ * ℓ * q) (by ring) φ hφ
  rw [key]
  by_cases hd : ℓ ∣ N₀
  · simp [hd, h.mpr hd]
  · simp [hd, mt h.mp hd]
