import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
    {m N : ℕ} [NeZero m]
    {f : CuspForm (CongruenceSubgroup.Gamma0 m) 2}
    (hN : 1 < N)
    (hf : ∀ n : ℕ, Nat.Coprime n N → ModularFormClass.qCoeff f n = 0) :
    f ∈ Submodule.span ℂ
      {F : CuspForm (CongruenceSubgroup.Gamma0 m) 2 |
        ∃ (q R : ℕ) (hqR : q * R ∣ m) (fq : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
          q.Prime ∧ q * R = m ∧ F = FreyPackage.ModMCarrier.rescaleLin hqR 2 fq} := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero.solution
