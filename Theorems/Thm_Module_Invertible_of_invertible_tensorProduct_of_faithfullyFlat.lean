import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat

universe u v w
theorem Module.Invertible.of_invertible_tensorProduct_of_faithfullyFlat
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Invertible S (TensorProduct R S M)] :
    Module.Invertible R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_invertible_tensorProduct_of_faithfullyFlat.solution
