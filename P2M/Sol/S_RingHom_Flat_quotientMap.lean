import Mathlib
import P2M.Util
namespace P2MW.S_RingHom_Flat_quotientMap

set_option autoImplicit false

theorem solution
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) (I : Ideal R) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Flat R S := hf
  have key : Module.Flat (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact RingHom.flat_algebraMap_iff.mpr key
