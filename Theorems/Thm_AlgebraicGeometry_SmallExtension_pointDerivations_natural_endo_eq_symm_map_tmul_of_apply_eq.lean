import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem AlgebraicGeometry.SmallExtension.pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)

    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))

    (θ : W →ₗ[k] W)
    (η : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) →ₗ[k] ↥(Algebra.PointDerivations k A ev M))
    (hηnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      η M' (Algebra.PointDerivations.map ev g δ) = Algebra.PointDerivations.map ev g (η M δ))
    (hηpin : ∀ δ : ↥(Algebra.PointDerivations k A ev k),
      Φ k (η k δ) = TensorProduct.map θ (LinearMap.id : k →ₗ[k] k) (Φ k δ))
    (M : Type u) [AddCommGroup M] [Module k M] (δ : ↥(Algebra.PointDerivations k A ev M)) :
    η M δ = (Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq.solution
