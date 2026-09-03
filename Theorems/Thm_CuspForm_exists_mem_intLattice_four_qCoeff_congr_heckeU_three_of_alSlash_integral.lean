import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import P2M.Util
import P2M.Sol.S_CuspForm_exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral
    {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M 3) (hq : ∃ q : ℕ, q.Prime ∧ q ∣ A.R ∧ q % 3 = 2)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ 3)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (3 : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R 4, ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 3 ⇑f) n = (3 : ℂ) * m := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_mem_intLattice_four_qCoeff_congr_heckeU_three_of_alSlash_integral.solution
