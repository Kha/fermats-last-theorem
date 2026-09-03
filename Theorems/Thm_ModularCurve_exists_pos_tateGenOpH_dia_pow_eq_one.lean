import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_pos_tateGenOpH_dia_pow_eq_one
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

theorem ModularCurve.exists_pos_tateGenOpH_dia_pow_eq_one
    (N p : ℕ) [NeZero N] [Fact p.Prime] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ) (d : (ZMod N)ˣ) :
    ∃ m : ℕ, 0 < m ∧ (ModularCurve.tateGenOpH N H S p (.dia d)) ^ m = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_pos_tateGenOpH_dia_pow_eq_one.solution
