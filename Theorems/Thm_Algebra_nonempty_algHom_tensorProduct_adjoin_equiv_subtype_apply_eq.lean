import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq
    {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] (a : B)
    (F : Type*) [CommRing F] [Algebra (Algebra.adjoin A ({a} : Set B)) F]
    (T : Type*) [CommRing T] [Algebra A T] [Algebra F T] [Algebra (Algebra.adjoin A ({a} : Set B)) T]
    [IsScalarTower (Algebra.adjoin A ({a} : Set B)) F T] [IsScalarTower A (Algebra.adjoin A ({a} : Set B)) T] :
    Nonempty ((F ⊗[Algebra.adjoin A ({a} : Set B)] B →ₐ[F] T) ≃
      {φ : B →ₐ[A] T // φ a = algebraMap (Algebra.adjoin A ({a} : Set B)) T ⟨a, Algebra.self_mem_adjoin_singleton A a⟩}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_nonempty_algHom_tensorProduct_adjoin_equiv_subtype_apply_eq.solution
