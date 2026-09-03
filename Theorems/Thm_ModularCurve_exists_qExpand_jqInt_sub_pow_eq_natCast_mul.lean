import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

p2m_open "ModularCurve~qExpand_jqModC_eq_pow_unconditional"

theorem ModularCurve.exists_qExpand_jqInt_sub_pow_eq_natCast_mul (q : ℕ) [Fact q.Prime] :
    ∃ h : LaurentSeries ℤ, qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * h := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul.solution
