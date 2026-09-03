import Definitions.Def_CuspForm_Petersson
import P2M.Util
import P2M.Sol.S_CuspForm_petersson_add_left
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

theorem CuspForm.petersson_add_left {N : ℕ} {k : ℤ} [NeZero N]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ + f₂) g = CuspForm.petersson f₁ g + CuspForm.petersson f₂ g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_petersson_add_left.solution
