import Mathlib
import Definitions.Def_CuspForm_PeterssonOn
import P2M.Util
import P2M.Sol.S_CuspForm_peterssonOn_add_smul_conj
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.peterssonOn_add_smul_conj (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.solution
