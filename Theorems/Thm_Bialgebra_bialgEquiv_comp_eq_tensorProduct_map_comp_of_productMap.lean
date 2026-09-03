import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_bialgEquiv_comp_eq_tensorProduct_map_comp_of_productMap

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.bialgEquiv_comp_eq_tensorProduct_map_comp_of_productMap
    (k : Type*) [Field k] {A C A' C' : Type*} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
    [Bialgebra k A] [Bialgebra k C] [Bialgebra k A'] [Bialgebra k C']
    (ρ₀ ρ₁ : A →ₐc[k] C) (ρ₀' ρ₁' : A' →ₐc[k] C')
    (κ : C ≃ₐc[k] A ⊗[k] A) (κ' : C' ≃ₐc[k] A' ⊗[k] A')
    (hκ : ∀ x : A ⊗[k] A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x)
    (hκ' : ∀ x : A' ⊗[k] A', κ'.symm x = Algebra.TensorProduct.productMap (ρ₀' : A' →ₐ[k] C') (ρ₁' : A' →ₐ[k] C') x)
    (tA : A' →ₐc[k] A) (tC : C' →ₐc[k] C)
    (h₀ : ∀ a : A', tC (ρ₀' a) = ρ₀ (tA a)) (h₁ : ∀ a : A', tC (ρ₁' a) = ρ₁ (tA a)) :
    (κ : C →ₐc[k] A ⊗[k] A).comp tC = (Bialgebra.TensorProduct.map tA tA).comp (κ' : C' →ₐc[k] A' ⊗[k] A') := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_bialgEquiv_comp_eq_tensorProduct_map_comp_of_productMap.solution
