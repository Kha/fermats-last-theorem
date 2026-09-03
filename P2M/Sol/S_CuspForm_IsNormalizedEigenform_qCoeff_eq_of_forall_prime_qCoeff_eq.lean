import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_qCoeff_zero
import P2M.Util
namespace P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq

open ModularFormClass

theorem solution {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) (n : ℕ) :
    qCoeff f n = qCoeff g n := by
  have hpow : ∀ {p : ℕ}, p.Prime → qCoeff f p = qCoeff g p →
      ∀ j : ℕ, qCoeff f (p ^ j) = qCoeff g (p ^ j) := by
    intro p hp hfg j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      match j, IH with
      | 0, _ => rw [pow_zero, hf.qCoeff_one, hg.qCoeff_one]
      | 1, _ => rw [pow_one]; exact hfg
      | (m + 2), IH =>
        have h1 : qCoeff f (p ^ (m + 1)) = qCoeff g (p ^ (m + 1)) := IH (m + 1) (by omega)
        have h0 : qCoeff f (p ^ m) = qCoeff g (p ^ m) := IH m (by omega)
        by_cases hpN : p ∣ N
        · rw [hf.qCoeff_prime_pow_of_dvd p m hp hpN, hg.qCoeff_prime_pow_of_dvd p m hp hpN, hfg, h1]
        · rw [hf.qCoeff_prime_pow_of_not_dvd p m hp hpN,
            hg.qCoeff_prime_pow_of_not_dvd p m hp hpN, hfg, h1, h0]
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp _ => exact hpow hp (h p hp) j
  | zero => exact (CuspForm.qCoeff_zero f).trans (CuspForm.qCoeff_zero g).symm
  | one => exact hf.qCoeff_one.trans hg.qCoeff_one.symm
  | coprime a b _ _ hab iha ihb =>
    rw [hf.qCoeff_mul_of_coprime a b hab, hg.qCoeff_mul_of_coprime a b hab, iha, ihb]
