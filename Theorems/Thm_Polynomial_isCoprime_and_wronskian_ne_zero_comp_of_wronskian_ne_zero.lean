import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero

theorem Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero {k : Type*} [Field k] [IsAlgClosed k] {u v s t U V : Polynomial k} (huv : IsCoprime u v) (hu : 0 < max u.natDegree v.natDegree) (hw : Polynomial.wronskian u v ≠ 0) (hst : IsCoprime s t) (hs : 0 < max s.natDegree t.natDegree) (hw' : Polynomial.wronskian s t ≠ 0) (hU : ∀ x : k, v.eval x ≠ 0 → U.eval x = v.eval x ^ max s.natDegree t.natDegree * s.eval (u.eval x / v.eval x)) (hV : ∀ x : k, v.eval x ≠ 0 → V.eval x = v.eval x ^ max s.natDegree t.natDegree * t.eval (u.eval x / v.eval x)) : IsCoprime U V ∧ 0 < max U.natDegree V.natDegree ∧ Polynomial.wronskian U V ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero.solution
