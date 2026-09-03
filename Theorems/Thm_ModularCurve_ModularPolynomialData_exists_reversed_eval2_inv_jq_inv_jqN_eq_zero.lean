import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one

open ModularCurve Polynomial

theorem ModularCurve.ModularPolynomialData.exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Ψ : Polynomial (Polynomial ℤ),
      (∀ i j : ℕ, (Ψ.coeff i).coeff j =
        if i ≤ p + 1 ∧ j ≤ p + 1 then (data.Φ.coeff (p + 1 - i)).coeff (p + 1 - j) else 0) ∧
      Ψ.natDegree = p + 1 ∧
      (Ψ.coeff (p + 1)).coeff 0 = 1 ∧
      Ψ.coeff 0 = X ^ (p + 1) ∧
      swapBivar Ψ = Ψ ∧
      Ψ.eval₂ (Polynomial.aeval (R := ℤ) jq⁻¹).toRingHom (jqN p)⁻¹ = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero.solution
