import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularForm.dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff (p ℓ : ℕ) [Fact p.Prime]
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hℓp : ℓ ≠ p) (h : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (b : ℕ → ℤ) (hb : ∀ n : ℕ, (b n : ℂ) = ModularFormClass.qCoeff h n)
    (hdvd : ∀ n : ℕ, n ≠ 0 → (ℓ : ℤ) ∣ b n) : (ℓ : ℤ) ∣ b 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_dvd_qCoeff_zero_of_prime_ne_level_dvd_qCoeff.solution
