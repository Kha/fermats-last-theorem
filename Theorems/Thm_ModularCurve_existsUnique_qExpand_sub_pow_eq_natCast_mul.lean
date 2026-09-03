import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
attribute [-simp] ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve
theorem ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul
    (q : ℕ) [Fact q.Prime] (f : LaurentSeries ℤ) :
    ∃! S : LaurentSeries ℤ, qExpand ℤ q f - f ^ q = (q : LaurentSeries ℤ) * S := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul.solution
