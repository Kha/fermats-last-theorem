import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
    (k : Type*) [Field k] (A C : Type*) [CommRing A] [CommRing C] [Bialgebra k A] [Bialgebra k C]
    [FiniteDimensional k A] [FiniteDimensional k C]
    (ρ₀ ρ₁ : A →ₐc[k] C)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C)))
    (hrank : Module.finrank k C = Module.finrank k A * Module.finrank k A) :
    ∃ κ : C ≃ₐc[k] A ⊗[k] A,
      (∀ a : A, κ.symm (a ⊗ₜ[k] 1) = ρ₀ a) ∧ (∀ a : A, κ.symm (1 ⊗ₜ[k] a) = ρ₁ a) ∧
      ∀ x : A ⊗[k] A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq.solution
