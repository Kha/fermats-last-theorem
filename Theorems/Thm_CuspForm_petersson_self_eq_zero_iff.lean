import Definitions.Def_CuspForm_Petersson
import P2M.Util
import P2M.Sol.S_CuspForm_petersson_self_eq_zero_iff
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

theorem CuspForm.petersson_self_eq_zero_iff {N : ℕ} {k : ℤ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = 0 ↔ f = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_petersson_self_eq_zero_iff.solution
