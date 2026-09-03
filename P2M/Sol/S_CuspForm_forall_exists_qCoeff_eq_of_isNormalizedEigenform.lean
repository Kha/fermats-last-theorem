import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Theorems.Thm_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
import Theorems.Thm_CuspForm_qCoeff_zero
import P2M.Util
namespace P2MW.S_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

open CuspForm

set_option autoImplicit false

theorem solution {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform) :
    ∀ n : ℕ, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g n := by
  have hprime := hg.primeCoeffsIntegral_of_neZero
  have hpow : ∀ ℓ : ℕ, ℓ.Prime → ∀ r : ℕ, ∃ a : integralClosure ℤ ℂ,
      (a : ℂ) = ModularFormClass.qCoeff g (ℓ ^ r) := by
    intro ℓ hℓ r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      rcases r with _ | (_ | s)
      · exact ⟨1, by simpa [pow_zero] using hg.qCoeff_one.symm⟩
      · simpa [pow_one] using hprime ⟨ℓ, hℓ⟩
      · obtain ⟨a1, ha1⟩ := ih (s + 1) (by omega)
        obtain ⟨a0, ha0⟩ := ih s (by omega)
        obtain ⟨aℓ, haℓ⟩ := hprime ⟨ℓ, hℓ⟩
        by_cases hdvd : ℓ ∣ N
        · refine ⟨aℓ * a1, ?_⟩
          rw [hg.qCoeff_prime_pow_of_dvd ℓ s hℓ hdvd]
          push_cast [haℓ, ha1]
          ring
        · refine ⟨aℓ * a1 - ℓ * a0, ?_⟩
          rw [hg.qCoeff_prime_pow_of_not_dvd ℓ s hℓ hdvd]
          push_cast [haℓ, ha1, ha0]
          ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | (_ | m)
    · exact ⟨0, by simpa using (CuspForm.qCoeff_zero g).symm⟩
    · exact ⟨1, by simpa using hg.qCoeff_one.symm⟩
    · set n := m + 2 with hndef
      have hn0 : n ≠ 0 := by omega
      have hn1 : n ≠ 1 := by omega
      set ℓ := n.minFac with hℓdef
      have hℓp : ℓ.Prime := Nat.minFac_prime hn1
      have hℓ2 : 2 ≤ ℓ := hℓp.two_le
      have he1 : 1 ≤ n.factorization ℓ :=
        (Nat.Prime.pow_dvd_iff_le_factorization hℓp hn0).mp (by simpa using n.minFac_dvd)
      have hone : 1 < ℓ ^ n.factorization ℓ := by
        calc 1 < ℓ := hℓ2
          _ = ℓ ^ 1 := (pow_one ℓ).symm
          _ ≤ ℓ ^ n.factorization ℓ := Nat.pow_le_pow_right (by omega) he1
      have hlt : n / ℓ ^ n.factorization ℓ < n :=
        Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hone
      have hcop : Nat.Coprime (ℓ ^ n.factorization ℓ) (n / ℓ ^ n.factorization ℓ) :=
        (Nat.coprime_ordCompl hℓp hn0).pow_left _
      have hsplit : n = ℓ ^ n.factorization ℓ * (n / ℓ ^ n.factorization ℓ) :=
        (Nat.ordProj_mul_ordCompl_eq_self n ℓ).symm
      obtain ⟨am, ham⟩ := ih (n / ℓ ^ n.factorization ℓ) hlt
      obtain ⟨ap, hap⟩ := hpow ℓ hℓp (n.factorization ℓ)
      refine ⟨ap * am, ?_⟩
      conv_rhs => rw [hsplit, hg.qCoeff_mul_of_coprime _ _ hcop]
      push_cast [hap, ham]
      ring
