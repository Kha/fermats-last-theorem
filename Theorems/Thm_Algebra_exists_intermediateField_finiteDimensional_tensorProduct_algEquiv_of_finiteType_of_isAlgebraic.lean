import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Algebra.exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (A : Type w) [CommRing A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra L A₀) (_ : Algebra.FiniteType L A₀),
      Nonempty ((K ⊗[L] A₀) ≃ₐ[K] A) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_intermediateField_finiteDimensional_tensorProduct_algEquiv_of_finiteType_of_isAlgebraic.solution
