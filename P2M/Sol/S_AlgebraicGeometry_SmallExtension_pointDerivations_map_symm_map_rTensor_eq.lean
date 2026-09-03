import Mathlib
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)
    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))
    (θ : W →ₗ[k] W)
    (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
    (δ : ↥(Algebra.PointDerivations k A ev M)) :
    Algebra.PointDerivations.map ev g ((Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ))) =
      (Φ M').symm (TensorProduct.map θ (LinearMap.id : M' →ₗ[k] M') (Φ M' (Algebra.PointDerivations.map ev g δ))) := by
  apply (Φ M').injective
  rw [hΦnat, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hΦnat, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp,
    LinearMap.comp_id]
