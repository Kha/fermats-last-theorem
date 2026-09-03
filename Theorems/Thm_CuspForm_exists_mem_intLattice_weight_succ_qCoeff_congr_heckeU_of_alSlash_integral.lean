import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ p)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (p : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R ((p : ℤ) + 1), ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑f) n = (p : ℂ) * m := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral.solution
