import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_qCoeff_zero
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff
import P2M.Util
namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff_nat
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open ModularFormClass

theorem solution {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (n : ℕ) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f n := by
  suffices h : ∀ n : ℕ, qCoeff f n ∈ integralClosure ℤ ℂ from ⟨⟨_, h n⟩, rfl⟩
  have hprime : ∀ p : ℕ, p.Prime → qCoeff f p ∈ integralClosure ℤ ℂ := fun p hp ↦ by
    obtain ⟨a, ha⟩ := hf.exists_integralClosure_coe_eq_qCoeff hN p hp
    exact ha ▸ a.2
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => rw [CuspForm.qCoeff_zero f]; exact zero_mem _
  | prime_pow p e hp =>

    suffices H : ∀ e : ℕ, qCoeff f (p ^ e) ∈ integralClosure ℤ ℂ ∧
        qCoeff f (p ^ (e + 1)) ∈ integralClosure ℤ ℂ from (H e).1
    intro e
    induction e with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, hf.qCoeff_one]; exact one_mem _
      · rw [zero_add, pow_one]; exact hprime p hp
    | succ e ih =>
      refine ⟨ih.2, ?_⟩
      by_cases hpN : p ∣ N
      · rw [hf.qCoeff_prime_pow_of_dvd p e hp hpN]
        exact mul_mem (hprime p hp) ih.2
      · rw [hf.qCoeff_prime_pow_of_not_dvd p e hp hpN]
        exact sub_mem (mul_mem (hprime p hp) ih.2) (mul_mem (natCast_mem _ p) ih.1)
  | coprime a b _ _ hab iha ihb =>
    rw [hf.qCoeff_mul_of_coprime a b hab]
    exact mul_mem iha ihb
