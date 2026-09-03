import Definitions.Def_CuspForm_Petersson
import P2M.Util
import P2M.Sol.S_CuspForm_petersson_self_re_nonneg
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

theorem CuspForm.petersson_self_re_nonneg {N : ℕ} {k : ℤ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    0 ≤ (CuspForm.petersson f f).re := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_petersson_self_re_nonneg.solution
