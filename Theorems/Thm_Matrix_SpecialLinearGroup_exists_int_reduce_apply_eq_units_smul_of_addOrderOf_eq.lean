import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex
attribute [-simp] CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq
    (m : ℕ) [NeZero m] (w : ZMod m × ZMod m) (hw : addOrderOf w = m) (a : (ZMod m)ˣ) :
    ∃ γ : SL(2, ℤ),
      ((γ 0 0 : ℤ) : ZMod m) * w.1 + ((γ 0 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.1 ∧
      ((γ 1 0 : ℤ) : ZMod m) * w.1 + ((γ 1 1 : ℤ) : ZMod m) * w.2 = (a : ZMod m) * w.2 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_int_reduce_apply_eq_units_smul_of_addOrderOf_eq.solution
