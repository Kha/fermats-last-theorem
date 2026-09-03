import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
    {q t : ℕ} (hq : q ≠ 0) (hqt : q ∣ t) {k : ℤ} (ε : DirichletCharacter ℂ t)
    (E : CuspForm (CongruenceSubgroup.Gamma1 (q * t)) k)
    (hE : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_mul_left t q) ε) E)
    {K : ℕ} (hK : K ≠ 0) (hKq : Nat.Coprime K q)
    (hzero : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff E n = 0)
    {N' : ℕ} (Φ : CuspForm (CongruenceSubgroup.Gamma1 N') k)
    (hΦ : ∀ τ : UpperHalfPlane, Φ τ = ∑ j ∈ Finset.range q,
        ((⇑E : UpperHalfPlane → ℂ) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * t) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ)
    (n : ℕ) (hn : Nat.Coprime n K) : ModularFormClass.qCoeff Φ n = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.solution
