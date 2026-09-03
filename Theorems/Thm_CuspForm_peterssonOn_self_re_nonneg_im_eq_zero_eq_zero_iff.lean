import Mathlib
import Definitions.Def_CuspForm_PeterssonOn
import P2M.Util
import P2M.Sol.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (k : ℤ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    0 ≤ (CuspForm.peterssonOn Γ k f f).re ∧ (CuspForm.peterssonOn Γ k f f).im = 0 ∧
    (CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.solution
