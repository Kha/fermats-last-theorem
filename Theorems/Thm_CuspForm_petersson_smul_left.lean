import Definitions.Def_CuspForm_Petersson
import P2M.Util
import P2M.Sol.S_CuspForm_petersson_smul_left
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

theorem CuspForm.petersson_smul_left {N : ℕ} {k : ℤ} [NeZero N]
    (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (c • f) g = starRingEnd ℂ c * CuspForm.petersson f g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_petersson_smul_left.solution
