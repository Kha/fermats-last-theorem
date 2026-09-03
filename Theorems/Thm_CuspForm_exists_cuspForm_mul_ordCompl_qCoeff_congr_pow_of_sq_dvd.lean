import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU
set_option autoImplicit false

theorem CuspForm.exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd (p : ℕ) [Fact p.Prime] {L : ℕ} [NeZero L] {v : ℕ} (hv : 2 ≤ v)
    (hvL : L.factorization p = v)
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    (hgint : ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g n) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 (p * (L / p ^ v))) (2 * (p : ℤ) ^ (v - 1)),
      (∀ n : ℕ, ∃ A : integralClosure ℤ ℂ, (A : ℂ) = ModularFormClass.qCoeff F n) ∧
      (∀ K : IntermediateField ℚ ℂ, (∀ n : ℕ, ModularFormClass.qCoeff g n ∈ K) →
        ∀ n : ℕ, ModularFormClass.qCoeff F n ∈ K) ∧
      (∀ (n : ℕ) (a A : integralClosure ℤ ℂ), (a : ℂ) = ModularFormClass.qCoeff g n →
        (A : ℂ) = ModularFormClass.qCoeff F n →
        A - a ^ p ^ (v - 1) ∈ Ideal.span {(p : integralClosure ℤ ℂ)}) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_cuspForm_mul_ordCompl_qCoeff_congr_pow_of_sq_dvd.solution
