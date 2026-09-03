import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import P2M.Util
import P2M.Sol.S_Matrix_det_diagonal_add_const_int
attribute [-simp] ModularCurve.coordOf_apply ModularCurve.coordOfEquiv_apply ModularCurve.diffChar_coe_apply ModularCurve.gramRangeBasisOf_coe ModularCurve.gramMatrixOf_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply

namespace Matrix
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
theorem det_diagonal_add_const_int (d : κ → ℤ) (c : ℤ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.of fun i j => (if i = j then d i else 0) + c).det =
      (∏ i, d i) + c * ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by p2m_exact_reverting @_root_.P2MW.S_Matrix_det_diagonal_add_const_int.solution
end Matrix
