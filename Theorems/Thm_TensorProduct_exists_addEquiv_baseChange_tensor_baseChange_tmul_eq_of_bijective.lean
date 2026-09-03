import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective

set_option autoImplicit false

universe u

open TensorProduct

theorem TensorProduct.exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective
    {k A B C : Type u} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra A C] [Algebra B C]
    [IsScalarTower k A C] [IsScalarTower k B C]
    (Φ : A ⊗[k] B ≃ₗ[k] C) (hΦ : ∀ (a : A) (b : B), Φ (a ⊗ₜ b) = algebraMap A C a * algebraMap B C b)
    (P : Type u) [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
    (Q : Type u) [AddCommGroup Q] [Module B Q] [Module k Q] [IsScalarTower k B Q] :
    ∃ g : (C ⊗[A] P) ⊗[C] (C ⊗[B] Q) ≃+ P ⊗[k] Q,
      ∀ (p : P) (q : Q), g (((1 : C) ⊗ₜ[A] p) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] q)) = p ⊗ₜ[k] q := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_exists_addEquiv_baseChange_tensor_baseChange_tmul_eq_of_bijective.solution
