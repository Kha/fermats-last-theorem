import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

theorem Algebra.TensorProduct.isReduced_of_perfectField_of_isReduced
    (k : Type u) [Field k] [PerfectField k] (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]
    (K : Type w) [Field K] [Algebra k K] :
    IsReduced (K ⊗[k] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_isReduced_of_perfectField_of_isReduced.solution
