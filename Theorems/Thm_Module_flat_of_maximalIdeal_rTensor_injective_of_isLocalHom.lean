import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u

theorem Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (h : Function.Injective (LinearMap.rTensor M (maximalIdeal A).subtype)) :
    Module.Flat A M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom.solution
