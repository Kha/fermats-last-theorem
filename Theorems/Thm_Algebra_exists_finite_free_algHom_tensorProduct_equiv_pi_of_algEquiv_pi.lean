import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi

set_option autoImplicit false

open scoped TensorProduct

universe u
theorem Algebra.exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (A' : Type u) [CommRing A'] [Algebra A A'] (d : ℕ) (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) :
    ∃ (F : Fin d → Type u) (_ : ∀ i, CommRing (F i)) (_ : ∀ i, Algebra A' (F i)),
      (∀ i, Module.Finite A' (F i)) ∧ (∀ i, Module.Free A' (F i)) ∧
      ∃ σ : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
          (H →ₐ[B] (B ⊗[A] T)) ≃ (∀ i, F i →ₐ[A'] T),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
          [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T'] (u : T →ₐ[A'] T')
          (g : H →ₐ[B] (B ⊗[A] T)),
          σ T' ((Algebra.TensorProduct.map (AlgHom.id B B) (u.restrictScalars A)).comp g)
            = fun i => u.comp (σ T g i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi.solution
