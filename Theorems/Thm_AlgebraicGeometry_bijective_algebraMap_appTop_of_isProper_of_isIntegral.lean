import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] [IsIntegral X] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_algebraMap_appTop_of_isProper_of_isIntegral.solution
