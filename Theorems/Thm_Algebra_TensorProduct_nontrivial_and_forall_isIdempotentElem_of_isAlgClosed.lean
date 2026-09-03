import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem Algebra.TensorProduct.nontrivial_and_forall_isIdempotentElem_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (R : Type u) [CommRing R] [Algebra k R]
    [Module.Finite k R] [Nontrivial R] (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (K : Type u) [Field K] [Algebra k K] :
    Nontrivial (K ⊗[k] R) ∧ ∀ e : K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed.solution
