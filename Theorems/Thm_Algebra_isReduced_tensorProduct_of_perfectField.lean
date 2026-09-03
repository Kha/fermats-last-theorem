import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isReduced_tensorProduct_of_perfectField

open scoped TensorProduct

universe u v w

theorem Algebra.isReduced_tensorProduct_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A] [IsReduced A]
    (L : Type w) [Field L] [Algebra k L] :
    IsReduced (L ⊗[k] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isReduced_tensorProduct_of_perfectField.solution
