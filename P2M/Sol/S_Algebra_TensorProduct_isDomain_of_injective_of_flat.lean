import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_TensorProduct_isDomain_of_injective_of_flat

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (R k A K : Type*) [CommRing R] [CommRing k] [Algebra R k] [Module.Flat R k]
    [CommRing A] [Algebra R A] [CommRing K] [Algebra R K]
    (f : A →ₐ[R] K) (hf : Function.Injective f) [IsDomain (k ⊗[R] K)] :
    IsDomain (k ⊗[R] A) := by

  let g : k ⊗[R] A →ₐ[k] k ⊗[R] K := Algebra.TensorProduct.map (AlgHom.id k k) f
  have hg : Function.Injective g := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := k) f.toLinearMap hf
    intro x y hxy
    apply h
    simp [g, LinearMap.lTensor] at hxy
    exact hxy

  haveI : Nontrivial (k ⊗[R] A) := g.toRingHom.domain_nontrivial
  exact hg.isDomain g.toRingHom
