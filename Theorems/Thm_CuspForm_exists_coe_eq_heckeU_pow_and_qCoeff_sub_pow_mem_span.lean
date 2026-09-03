import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU
set_option autoImplicit false
open ModularFormClass

theorem CuspForm.exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (hpM : p ^ 2 ∣ M) (k : ℤ)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) k)
    (hgint : ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = qCoeff g n) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 (M / p)) (p * k),
      ⇑F = ModularForm.heckeU (p * k) p ((⇑g) ^ p) ∧
      (∀ n : ℕ, ∃ A : integralClosure ℤ ℂ, (A : ℂ) = qCoeff F n) ∧
      (∀ K : IntermediateField ℚ ℂ, (∀ n : ℕ, qCoeff g n ∈ K) → ∀ n : ℕ, qCoeff F n ∈ K) ∧
      (∀ (n : ℕ) (a A : integralClosure ℤ ℂ), (a : ℂ) = qCoeff g n → (A : ℂ) = qCoeff F n →
        A - a ^ p ∈ Ideal.span {(p : integralClosure ℤ ℂ)}) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_coe_eq_heckeU_pow_and_qCoeff_sub_pow_mem_span.solution
