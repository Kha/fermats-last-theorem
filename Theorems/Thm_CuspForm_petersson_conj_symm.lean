import Definitions.Def_CuspForm_Petersson
import P2M.Util
import P2M.Sol.S_CuspForm_petersson_conj_symm
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

theorem CuspForm.petersson_conj_symm {N : ℕ} {k : ℤ} [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    starRingEnd ℂ (CuspForm.petersson g f) = CuspForm.petersson f g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_petersson_conj_symm.solution
