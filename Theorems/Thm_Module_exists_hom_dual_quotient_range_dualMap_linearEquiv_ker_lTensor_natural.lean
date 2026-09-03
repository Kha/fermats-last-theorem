import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
    (R : Type u) [CommRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁) :
    ∃ e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
        ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B),
      (∀ (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B'] (u : B →ₗ[R] B')
          (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
          ((e B' (u ∘ₗ g) : LinearMap.ker (d.lTensor B')) : B' ⊗[R] K₀) =
            u.rTensor K₀ ((e B g : LinearMap.ker (d.lTensor B)) : B ⊗[R] K₀)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)) (φ : Module.Dual R K₀),
          (e B).symm t (Submodule.Quotient.mk φ) = TensorProduct.rid R B (φ.lTensor B (t : B ⊗[R] K₀))) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural.solution
