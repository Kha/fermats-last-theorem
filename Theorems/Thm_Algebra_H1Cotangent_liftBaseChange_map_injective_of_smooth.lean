import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Smooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.solution
