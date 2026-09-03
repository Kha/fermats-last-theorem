import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_comap_maximalIdeal_rTensor_injective

open TensorProduct

theorem Module.flat_of_comap_maximalIdeal_rTensor_injective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (p : Ideal R) (hp : (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = p)
    (h : Function.Injective (p.subtype.rTensor M)) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_comap_maximalIdeal_rTensor_injective.solution
