import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Conj
import P2M.Util
import P2M.Sol.S_GL2F3_isConj_pow_three_of_orderOf_eq_eight

theorem GL2F3.isConj_pow_three_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3))
    (hg : orderOf g = 8) : IsConj g (g ^ 3) := by p2m_exact_reverting @_root_.P2MW.S_GL2F3_isConj_pow_three_of_orderOf_eq_eight.solution
