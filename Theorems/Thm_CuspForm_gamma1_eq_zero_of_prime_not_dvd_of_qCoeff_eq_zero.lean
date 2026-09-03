import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {N p : ℕ} [NeZero N] (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.solution
