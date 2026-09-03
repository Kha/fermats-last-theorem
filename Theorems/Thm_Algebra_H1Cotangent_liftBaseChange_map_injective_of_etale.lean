import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution
