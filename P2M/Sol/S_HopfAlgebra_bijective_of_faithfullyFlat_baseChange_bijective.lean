import Mathlib
import P2M.Util
namespace P2MW.S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective

set_option autoImplicit false

universe u v

theorem solution
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H') (hφ : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R')) :
    Function.Bijective φ := by
  have h : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.lTensor R') := by
    rwa [← LinearMap.baseChange_eq_ltensor]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R R' _).mp h
