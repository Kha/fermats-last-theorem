import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {F F' : Type*} [Field F] [Field F'] [Algebra A F] [IsFractionRing A F]
    [Algebra B F'] [IsFractionRing B F'] (φ : F →+* F')
    (hφ : ∀ a : A, algebraMap B F' (algebraMap A B a) = φ (algebraMap A F a)) :
    Module.finrank K (K ⊗[A] B) = @Module.finrank F F' _ _ φ.toAlgebra.toModule := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite.solution
