import Mathlib
import P2M.Util
namespace P2MW.S_HopfAlgebra_eq_of_baseChange_eq

universe u v

set_option autoImplicit false

open scoped TensorProduct

namespace HopfAlgebra
namespace EqOfBaseChange
p2m_open "HopfAlgebra"

theorem tmul_one_injective
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Function.Injective (fun y : M => (1 : K) ⊗ₜ[R] y) := by
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have key : ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm a) =
      ((Algebra.linearMap R K).rTensor M) ((TensorProduct.lid R M).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  exact (TensorProduct.lid R M).symm.injective (h1 key)

end HopfAlgebra.EqOfBaseChange

open HopfAlgebra.EqOfBaseChange in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ ψ : H →ₐc[R] H')
    (h : (φ : H →ₐ[R] H').toLinearMap.baseChange K = (ψ : H →ₐ[R] H').toLinearMap.baseChange K) :
    φ = ψ := by
  refine DFunLike.ext _ _ fun x => ?_
  have hx := LinearMap.congr_fun h ((1 : K) ⊗ₜ[R] x)
  simp only [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply] at hx
  exact tmul_one_injective K H' hx
