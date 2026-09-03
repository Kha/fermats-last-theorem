import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ

open scoped MatrixGroups

theorem ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f)
    (hdvd : ∀ n : ℕ, 1 ≤ n → (ℓ : ℤ) ∣ T.coeff n)
    (h0 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T) :
    ((ℓ - 1 : ℕ) : ℤ) ∣ k := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_sub_one_dvd_weight_of_qExpansion_congr_const_levelOne.solution
