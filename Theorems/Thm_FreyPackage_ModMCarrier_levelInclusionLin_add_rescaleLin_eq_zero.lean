import Mathlib
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import P2M.Util
import P2M.Sol.S_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
attribute [-instance] Ihara.instGroupIharaAmalgam
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway

open CongruenceSubgroup FreyPackage.ModMCarrier
open scoped ModularForm MatrixGroups
theorem FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
    {R M q' : ℕ} [NeZero M] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (hRM : R ∣ M) (hqRM : q' * R ∣ M)
    (x y : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (h : levelInclusionLin hRM 2 x + rescaleLin hqRM 2 y = 0) : x = 0 ∧ y = 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero.solution
