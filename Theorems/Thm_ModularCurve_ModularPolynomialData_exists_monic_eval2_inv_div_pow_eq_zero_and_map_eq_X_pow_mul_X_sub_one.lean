import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

set_option autoImplicit false

open Polynomial ModularCurve

theorem ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Q : Polynomial (Polynomial ℤ), Q.Monic ∧ Q.natDegree = p + 1 ∧
      (∀ (S : Type*) [Field S] (x y : S), x ≠ 0 →
          data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y = 0 →
          Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) = 0) ∧
      (∀ (R : Type*) [CommRing R] [CharP R p],
          Q.map (Polynomial.eval₂RingHom (Int.castRingHom R) 0) = Polynomial.X ^ p * (Polynomial.X - 1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one.solution
