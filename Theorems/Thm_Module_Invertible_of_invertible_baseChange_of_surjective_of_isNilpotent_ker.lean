import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.Invertible.of_invertible_baseChange_of_surjective_of_isNilpotent_ker
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hπ : Function.Surjective (algebraMap R S)) (hker : IsNilpotent (RingHom.ker (algebraMap R S)))
    (P : Type w) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (h : Module.Invertible S (S ⊗[R] P)) : Module.Invertible R P := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_of_invertible_baseChange_of_surjective_of_isNilpotent_ker.solution
