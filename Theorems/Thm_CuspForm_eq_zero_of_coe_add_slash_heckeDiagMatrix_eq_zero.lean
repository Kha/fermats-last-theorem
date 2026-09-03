import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups
theorem CuspForm.eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (x y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : (⇑x : ℍ → ℂ) + ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') = 0) :
    x = 0 ∧ y = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_eq_zero_of_coe_add_slash_heckeDiagMatrix_eq_zero.solution
